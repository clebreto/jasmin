/* Differential test of the Armv8-M instruction semantics: see README.md. */

#ifndef RUNNER_H
#define RUNNER_H

#include <stdint.h>

#define NB_REGS 13      /* r0 to r12 */
#define SCRATCH_SIZE 32 /* bytes */

struct form {
  void (*stub)(void);  /* the instruction, as a function */
  const char *text;    /* the instruction, as printed by the compiler */
  uint16_t nb_rows;
  uint16_t in_mask;    /* registers whose value is given by the rows */
  uint16_t out_mask;   /* registers that the instruction writes */
  uint16_t base_mask;  /* registers holding an address in the scratch buffer */
  uint16_t mem;        /* the rows give the memory, before and after */
  uint32_t first;      /* index in test_data of the first row */
};

/* Layout of a row in test_data:
   - the value of each register of in_mask, in increasing order;
   - the flags: NZCV before in bits 3:0, NZCV after in bits 7:4, and in bits
     11:8 the flags that the model defines;
   - the expected value of each register of out_mask, in increasing order;
   - if mem is set, the scratch buffer before, then the scratch buffer after. */

extern const uint32_t test_data[];
extern const struct form test_forms[];
extern const uint32_t test_nb_forms;
extern const uint32_t test_nb_rows;

#endif
