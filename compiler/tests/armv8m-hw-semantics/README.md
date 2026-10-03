# Armv8-M hardware-semantics differential test

Checks that the semantics of the instructions of the Arm M-profile model
(`proofs/compiler/arm_instr_decl.v`), at the Armv8-M version, is what a
processor computes.

The reference is the Armv8-M Architecture Reference Manual (DDI0553B.r). The
model is taken at its ARMv8.1-M version: the instructions of ARMv7-M, which
also run on a Cortex-M4 (`ARCHFLAGS="-mcpu=cortex-m4 -mthumb"`) and on a
Cortex-M33 (the conditional selects are then reported as faulting), and the
conditional selects, which need a Cortex-M55:
`ARCHFLAGS="-mcpu=cortex-m55+nofp+nomve -mthumb"`, and, with QEMU, the machine
`mps3-an547` (`QEMU_MACHINE=mps3-an547 QEMU_LD=mps3-an547.ld`).

## Running the test

On the NXP LPC55S69-EVK, plugged through its debug probe
([probe-rs](https://probe.rs) flashes the board, runs the test and prints its
output):

```
make -C compiler check-armv8m-semantics         # from the repository root
make check-board                                # from this directory
```

On an emulated Cortex-M33 (QEMU, machine `mps2-an505` by default; the linker
script of this machine has not been tested, the test ran on a model of the
LPC55S69-EVK, with `QEMU_MACHINE=lpc55s69evk QEMU_LD=lpc55s69.ld`):

```
make -C compiler check-armv8m-semantics-qemu    # from the repository root
make check-qemu                                 # from this directory
```

Both need the GNU Arm embedded toolchain (`arm-none-eabi-gcc`); no C library
is used. The variables `CROSS`, `PROBE_RS`, `CHIP`, `QEMU`, `QEMU_MACHINE` and
`QEMU_LD` (the linker script of the emulated machine) configure the tools.

The test ends with `RESULT: PASS` or `RESULT: FAIL`, after the list of the
instructions that behave differently, with the inputs of their first failing
rows.

## How it works

`gen_armv8m_hw_semantics.ml` is linked against the compiler, hence against
the extraction of the model.

1. It enumerates the mnemonics of the model with their options: setting the
   flags, shifting the last operand (every kind of shift), conditional
   execution (every condition for `MOV` and `ADD`, four conditions for the
   other instructions).
2. For each of them, it enumerates the operands that the model accepts
   (`id_args_kinds`): registers (low ones and high ones), immediates that
   satisfy the conditions of the model, memory operands (with an immediate
   offset, a register offset, a scaled register offset).
3. Each instruction form becomes a function of one instruction in an assembly
   program that is printed by the assembly printer of the compiler
   (`Pp_arm_m4`): the instructions that run are the ones that `jasminc`
   emits, with their suffixes and their IT instructions.
4. It runs the assembler on this program. The instructions that the assembler
   rejects are instructions that the model accepts and that do not exist: they
   are listed, and left out.
5. It computes the expected result of each form on edge-case and
   pseudo-random inputs (registers, flags, memory), with the semantics of the
   model. This follows the semantics of assembly programs
   (`eval_instr_op` and `mem_write_vals` in `proofs/arch/arch_sem.v`): the
   operands are read as `id_in` describes, `id_semi` is applied, the results
   are written as `id_out` describes.

`runner.c` runs on the processor. For each row, it sets the registers r0 to
r12, the flags and a scratch buffer, calls the function, and compares the
whole state with the expected one: the registers that the instruction does
not write must be unchanged, as the flags; the flags that the model leaves
undefined are not compared. A fault (for instance, an undefined instruction)
is reported as a failure of the row.

## What is not tested

- `ADR`: the address is relative to the program counter.
- `LR` and `SP` as operands: the functions return through `LR` and run on the
  stack of the runner.
- The instructions that the compiler emits outside of the model: branches,
  calls, returns, `PUSH` and `POP`.

The skipped forms are listed at the beginning of `gen/tables.c`.
