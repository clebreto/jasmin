# ARMv8-A hardware-semantics differential test

Checks that the semantics of every ARMv8-A instruction modeled in
`proofs/compiler/armv8a_instr_decl.v` matches what the hardware actually
computes.

**Requires an AArch64 (ARMv8-A) host** (e.g. an Apple Silicon or other
ARMv8 machine); the generated program refuses to compile elsewhere.

Run with:

```
make -C compiler check-armv8a-semantics    # from the repository root
make check                                 # from this directory
```

## How it works

`gen_armv8a_hw_semantics.ml` (a dune executable linked against the
compiler library, hence against the OCaml extraction of the Coq model in
`src/CIL/armv8a_instr_decl.ml`):

1. enumerates every mnemonic of `armv8a_mnemonics` at both operand sizes
   (U32/W and U64/X), keeping the forms with `id_valid`, plus the
   shifted-register variants (`has_shift`) for every encodable shift
   kind and several shift amounts;
2. builds edge-case (0, 1, all-ones, sign bit, INT_MIN/-1, division by
   zero, out-of-range shift amounts, ...) and pseudo-random (fixed-seed
   splitmix64) operand vectors;
3. computes the expected outputs — result words *and* NZCV flags — by
   evaluating the extracted `id_semi` on Jasmin values (`app_sopn`);
4. emits a C program in which each instruction form is executed by an
   inline-asm statement over a table of operand rows; flags are read
   back with `mrs nzcv` and driven in with `msr nzcv`; loads/stores run
   against a scratch buffer. Every mismatch is reported with the
   instruction, inputs, expected and actual values; the process exits
   nonzero if any check fails.

Immediate operands that are part of the semantics (shift amounts,
bitfield lsb/width, MOVZ/MOVN/MOVK immediates) are enumerated over their
*encodable* ranges only. The skips (and why they are sound) are listed
in the header of the generated C file and in the header comment of the
generator.
