/* Differential test of the Armv8-M instruction semantics: see README.md.

   Runs every row of every instruction form on the processor, and compares the
   registers, the flags and the memory with the predictions of the model. */

#include "runner.h"

/* -------------------------------------------------------------------- */
/* Output: semihosting, or RTT (read by the debug probe). */

static uint32_t semihosting(uint32_t op, const void *arg) {
  register uint32_t r0 __asm__("r0") = op;
  register const void *r1 __asm__("r1") = arg;
  __asm__ volatile("bkpt 0xab" : "+r"(r0) : "r"(r1) : "memory");
  return r0;
}

#ifdef OUTPUT_RTT

#define RTT_SIZE 1024

struct rtt_buffer {
  const char *name;
  char *buffer;
  uint32_t size;
  volatile uint32_t write;
  volatile uint32_t read;
  uint32_t flags;
};

struct rtt_control {
  char id[16];
  int32_t nb_up;
  int32_t nb_down;
  struct rtt_buffer up[1];
  struct rtt_buffer down[1];
};

struct rtt_control _SEGGER_RTT;
static char rtt_up[RTT_SIZE];
static char rtt_down[16];

static void out_init(void) {
  static const char id[] = "SEGGER RTT";
  _SEGGER_RTT.nb_up = 1;
  _SEGGER_RTT.nb_down = 1;
  _SEGGER_RTT.up[0].name = "Terminal";
  _SEGGER_RTT.up[0].buffer = rtt_up;
  _SEGGER_RTT.up[0].size = RTT_SIZE;
  _SEGGER_RTT.up[0].flags = 2; /* block when the buffer is full */
  _SEGGER_RTT.down[0].name = "Terminal";
  _SEGGER_RTT.down[0].buffer = rtt_down;
  _SEGGER_RTT.down[0].size = sizeof rtt_down;
  /* The identifier is written last, and not as a whole: the probe looks for
     it in memory. */
  for (uint32_t i = 0; i < sizeof id; i++) _SEGGER_RTT.id[i] = id[i];
}

static void out_char(char c) {
  struct rtt_buffer *b = &_SEGGER_RTT.up[0];
  uint32_t next = b->write + 1;
  if (next == b->size) next = 0;
  while (next == b->read) {
  }
  b->buffer[b->write] = c;
  b->write = next;
}

static void out_flush(void) {
  struct rtt_buffer *b = &_SEGGER_RTT.up[0];
  while (b->write != b->read) {
  }
}

#else

static char out_buffer[128];
static uint32_t out_len;

static void out_init(void) { out_len = 0; }

static void out_flush(void) {
  out_buffer[out_len] = 0;
  if (out_len) semihosting(0x04 /* SYS_WRITE0 */, out_buffer);
  out_len = 0;
}

static void out_char(char c) {
  out_buffer[out_len++] = c;
  if (c == '\n' || out_len == sizeof out_buffer - 1) out_flush();
}

#endif

static void out_str(const char *s) {
  while (*s) out_char(*s++);
}

static void out_hex(uint32_t v) {
  for (int i = 28; i >= 0; i -= 4) out_char("0123456789abcdef"[(v >> i) & 0xf]);
}

static void out_dec(uint32_t v) {
  char d[10];
  int n = 0;
  do {
    d[n++] = (char)('0' + v % 10);
    v /= 10;
  } while (v);
  while (n) out_char(d[--n]);
}

static void out_flags(uint32_t f) {
  out_char(f & 8 ? 'N' : '-');
  out_char(f & 4 ? 'Z' : '-');
  out_char(f & 2 ? 'C' : '-');
  out_char(f & 1 ? 'V' : '-');
}

static void terminate(uint32_t failed) {
  static uint32_t block[2];
  out_flush();
  block[0] = 0x20026; /* ADP_Stopped_ApplicationExit */
  block[1] = failed ? 1 : 0;
  semihosting(0x20 /* SYS_EXIT_EXTENDED */, block);
  semihosting(0x18 /* SYS_EXIT */, (void *)(failed ? 0x20023u : 0x20026u));
  for (;;) {
  }
}

/* -------------------------------------------------------------------- */
/* Execution of one instruction. */

/* Registers r0 to r12, then the APSR. */
static uint32_t state_in[NB_REGS + 1];
static uint32_t state_out[NB_REGS + 1];

uint8_t scratch[SCRATCH_SIZE] __attribute__((aligned(8)));

/* Set by the fault handler. */
volatile uint32_t fault_taken;
uint32_t fault_sp;

__attribute__((naked, noinline)) static void
run_stub(void (*stub)(void), const uint32_t *in, uint32_t *out) {
  __asm__(
    "  push  {r4-r11, lr}\n"
    "  push  {r2}\n"               /* out */
    "  ldr   r3, =fault_sp\n"
    "  str   sp, [r3]\n"
    "  mov   lr, r0\n"
    "  ldr   r3, [r1, #52]\n"
    "  msr   apsr_nzcvq, r3\n"
    "  ldm   r1, {r0-r12}\n"
    "  blx   lr\n"
    "  push  {r0, r1}\n"
    "  mrs   r1, apsr\n"
    "  ldr   r0, [sp, #8]\n"       /* out */
    "  str   r1, [r0, #52]\n"
    "  add   r0, r0, #8\n"
    "  stm   r0, {r2-r12}\n"
    "  pop   {r1, r2}\n"           /* r0 and r1 of the instruction */
    "  strd  r1, r2, [r0, #-8]\n"
    "  .global fault_recover\n"
    "  .thumb_func\n"
    "fault_recover:\n"
    "  ldr   r3, =fault_sp\n"
    "  ldr   sp, [r3]\n"
    "  add   sp, sp, #4\n"
    "  pop   {r4-r11, pc}\n"
    "  .ltorg\n");
}

/* A fault in the instruction under test: return to the runner. */
extern void fault_recover(void);

void fault_handler_c(uint32_t *frame) {
  fault_taken = 1;
  frame[6] = (uint32_t)&fault_recover & ~1u; /* return address */
  frame[7] = 0x01000000;                     /* xPSR: Thumb state, no IT */
  /* Clear the fault status: UFSR, BFSR, MMFSR and HFSR. */
  *(volatile uint32_t *)0xe000ed28 = 0xffffffff;
  *(volatile uint32_t *)0xe000ed2c = 0xffffffff;
}

__attribute__((naked)) void fault_handler(void) {
  __asm__(
    "  tst   lr, #4\n"
    "  ite   eq\n"
    "  mrseq r0, msp\n"
    "  mrsne r0, psp\n"
    "  b     fault_handler_c\n");
}

/* -------------------------------------------------------------------- */

/* The first failing rows of a form are detailed. */
#define MAX_REPORTS 2

static uint32_t nb_reports;

static int report(const struct form *f, uint32_t row) {
  if (nb_reports >= MAX_REPORTS) return 0;
  out_str("  ");
  out_str(f->text);
  out_str(", row ");
  out_dec(row);
  out_str(": ");
  return 1;
}

static void report_inputs(const struct form *f) {
  out_str("    inputs:");
  for (int i = 0; i < NB_REGS; i++)
    if (f->in_mask & (1u << i)) {
      out_str(" r");
      out_dec((uint32_t)i);
      out_str("=");
      out_hex(state_in[i]);
    }
  out_str(" ");
  out_flags(state_in[NB_REGS] >> 28);
  out_str("\n");
}

int main(void) {
  uint32_t failed_forms = 0, failed_rows = 0, rows = 0;
  uint32_t expected[NB_REGS];

  out_init();
  out_str("Armv8-M instruction semantics: ");
  out_dec(test_nb_forms);
  out_str(" instruction forms, ");
  out_dec(test_nb_rows);
  out_str(" rows\n");

  for (uint32_t k = 0; k < test_nb_forms; k++) {
    const struct form *f = &test_forms[k];
    const uint32_t *p = &test_data[f->first];
    uint32_t form_failed = 0;

    nb_reports = 0;
    for (uint32_t row = 0; row < f->nb_rows; row++) {
      const uint8_t *mem_after = 0;
      uint32_t failed = 0;

      for (int i = 0; i < NB_REGS; i++) {
        if (f->in_mask & (1u << i)) {
          state_in[i] = *p++;
          if (f->base_mask & (1u << i)) state_in[i] += (uint32_t)scratch;
        } else {
          state_in[i] = 0xa5a50000u + (uint32_t)i * 0x0101u;
        }
        expected[i] = state_in[i];
      }
      uint32_t flags = *p++;
      uint32_t flags_in = flags & 0xf;
      uint32_t flags_out = (flags >> 4) & 0xf;
      uint32_t flags_mask = (flags >> 8) & 0xf;
      state_in[NB_REGS] = flags_in << 28;
      for (int i = 0; i < NB_REGS; i++)
        if (f->out_mask & (1u << i)) expected[i] = *p++;
      if (f->mem) {
        const uint8_t *mem_before = (const uint8_t *)p;
        for (int i = 0; i < SCRATCH_SIZE; i++) scratch[i] = mem_before[i];
        p += SCRATCH_SIZE / 4;
        mem_after = (const uint8_t *)p;
        p += SCRATCH_SIZE / 4;
      }

      fault_taken = 0;
      run_stub(f->stub, state_in, state_out);
      rows++;

      if (fault_taken) {
        if (report(f, row)) out_str("fault\n");
        failed = 1;
      } else {
        for (int i = 0; i < NB_REGS; i++)
          if (state_out[i] != expected[i]) {
            if (report(f, row)) {
              out_str("r");
              out_dec((uint32_t)i);
              out_str(" = ");
              out_hex(state_out[i]);
              out_str(", expected ");
              out_hex(expected[i]);
              out_str("\n");
            }
            failed = 1;
          }
        uint32_t flags_hw = state_out[NB_REGS] >> 28;
        if ((flags_hw ^ flags_out) & flags_mask) {
          if (report(f, row)) {
            out_str("flags = ");
            out_flags(flags_hw);
            out_str(", expected ");
            out_flags(flags_out);
            out_str(" (defined: ");
            out_flags(flags_mask);
            out_str(")\n");
          }
          failed = 1;
        }
        if (f->mem)
          for (int i = 0; i < SCRATCH_SIZE; i++)
            if (scratch[i] != mem_after[i]) {
              if (report(f, row)) {
                out_str("memory[");
                out_dec((uint32_t)i);
                out_str("] = ");
                out_hex(scratch[i]);
                out_str(", expected ");
                out_hex(mem_after[i]);
                out_str("\n");
              }
              failed = 1;
            }
      }
      if (failed) {
        if (nb_reports < MAX_REPORTS) report_inputs(f);
        nb_reports++;
        failed_rows++;
        form_failed++;
      }
    }
    if (form_failed) {
      out_str("FAIL ");
      out_str(f->text);
      out_str(": ");
      out_dec(form_failed);
      out_str(" rows out of ");
      out_dec(f->nb_rows);
      out_str("\n");
      failed_forms++;
    }
  }

  out_dec(rows);
  out_str(" rows executed, ");
  out_dec(failed_rows);
  out_str(" failed, in ");
  out_dec(failed_forms);
  out_str(" instruction forms\n");
  out_str(failed_rows || rows != test_nb_rows ? "RESULT: FAIL\n"
                                               : "RESULT: PASS\n");
  terminate(failed_rows || rows != test_nb_rows);
  return 0;
}

/* -------------------------------------------------------------------- */
/* Startup. */

extern uint32_t _stack_top, _data_load, _data_start, _data_end, _bss_start,
  _bss_end;

void reset_handler(void) {
  uint32_t *src = &_data_load, *dst = &_data_start;
  while (dst < &_data_end) *dst++ = *src++;
  for (dst = &_bss_start; dst < &_bss_end;) *dst++ = 0;
  main();
  for (;;) {
  }
}

__attribute__((section(".vectors"), used))
static void (*const vectors[16])(void) = {
  (void (*)(void))&_stack_top,
  reset_handler,
  fault_handler, /* NMI */
  fault_handler, /* HardFault */
  fault_handler, /* MemManage */
  fault_handler, /* BusFault */
  fault_handler, /* UsageFault */
  fault_handler, /* SecureFault */
  0, 0, 0,
  fault_handler, /* SVCall */
  fault_handler, /* DebugMonitor */
  0,
  fault_handler, /* PendSV */
  fault_handler, /* SysTick */
};
