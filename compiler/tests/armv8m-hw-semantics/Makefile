# Differential test of the Armv8-M instruction semantics against the
# hardware: see README.md.
#
# The generator (gen_armv8m_hw_semantics.ml) enumerates the instructions of
# the model (proofs/compiler/arm_instr_decl.v, at the Armv8-M version), prints
# them with the assembly printer of the compiler, and computes the expected
# results with the semantics of the model. The runner executes them on a
# Cortex-M33 and compares.
#
# Usage:
#   make check-board   on the NXP LPC55S69-EVK, through its debug probe
#   make check-qemu    on the Cortex-M33 emulated by QEMU

CROSS   ?= arm-none-eabi-
CC      := $(CROSS)gcc
OBJDUMP := $(CROSS)objdump
SIZE    := $(CROSS)size

# Armv8-M with the Main and DSP extensions
ARCHFLAGS := -mcpu=cortex-m33+nofp -mthumb
CFLAGS    := $(ARCHFLAGS) -Os -Wall -Wextra -ffreestanding -fno-builtin -g
LDFLAGS   := $(ARCHFLAGS) -nostdlib -nostartfiles -Wl,--gc-sections -L.

# The board, and the debug probe
PROBE_RS ?= probe-rs
CHIP     ?= LPC55S69JBD100

# The emulator
QEMU          ?= qemu-system-arm
QEMU_MACHINE  ?= mps2-an505
QEMU_LD       ?= $(QEMU_MACHINE).ld
QEMU_FLAGS    ?= -M $(QEMU_MACHINE) -nographic -serial none -monitor none \
                 -semihosting-config enable=on,target=native

GEN := gen

.PHONY: check-board check-qemu generate clean

check-board: $(GEN)/board.elf
	$(PROBE_RS) run --chip $(CHIP) $< 2>&1 | tee $(GEN)/board.log
	grep -q "^RESULT: PASS" $(GEN)/board.log

check-qemu: $(GEN)/qemu.elf
	$(QEMU) $(QEMU_FLAGS) -kernel $< 2>&1 | tee $(GEN)/qemu.log
	grep -q "^RESULT: PASS" $(GEN)/qemu.log

generate: $(GEN)/stubs.s

# The generator runs twice: the first file has every instruction that the
# model accepts, the second one leaves out the instructions that the assembler
# rejects (they are listed at the beginning of tables.c).
$(GEN)/stubs.s: gen_armv8m_hw_semantics.ml dune
	dune build ./gen_armv8m_hw_semantics.exe
	mkdir -p $(GEN)
	dune exec ./gen_armv8m_hw_semantics.exe -- $(GEN) > /dev/null
	-$(CC) $(ARCHFLAGS) -c -o $(GEN)/all.o $(GEN)/stubs.s 2> $(GEN)/assembler.log
	dune exec ./gen_armv8m_hw_semantics.exe -- $(GEN) $(GEN)/assembler.log

$(GEN)/tables.c: $(GEN)/stubs.s

$(GEN)/stubs.o: $(GEN)/stubs.s
	$(CC) $(ARCHFLAGS) -c -o $@ $<

$(GEN)/tables.o: $(GEN)/tables.c runner.h
	$(CC) $(CFLAGS) -I. -c -o $@ $<

$(GEN)/runner-rtt.o: runner.c runner.h
	mkdir -p $(GEN)
	$(CC) $(CFLAGS) -DOUTPUT_RTT -c -o $@ $<

$(GEN)/runner-semihosting.o: runner.c runner.h
	mkdir -p $(GEN)
	$(CC) $(CFLAGS) -c -o $@ $<

$(GEN)/board.elf: $(GEN)/runner-rtt.o $(GEN)/tables.o $(GEN)/stubs.o lpc55s69.ld sections.ld
	$(CC) $(LDFLAGS) -T lpc55s69.ld -o $@ $(GEN)/runner-rtt.o $(GEN)/tables.o $(GEN)/stubs.o
	$(SIZE) $@

$(GEN)/qemu.elf: $(GEN)/runner-semihosting.o $(GEN)/tables.o $(GEN)/stubs.o $(QEMU_LD) sections.ld
	$(CC) $(LDFLAGS) -T $(QEMU_LD) -o $@ $(GEN)/runner-semihosting.o $(GEN)/tables.o $(GEN)/stubs.o
	$(SIZE) $@

clean:
	rm -rf $(GEN)
