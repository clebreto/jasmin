# Differential test of the ARMv8-A instruction semantics against the
# hardware.
#
# The OCaml generator (gen_armv8a_hw_semantics.ml) evaluates the Coq
# semantics of every instruction modeled in
# proofs/compiler/armv8a_instr_decl.v (through the extracted code in
# src/CIL/armv8a_instr_decl.ml) on edge-case and pseudo-random operand
# vectors, and emits a C program that runs the same instructions natively
# and compares the results.
#
# REQUIREMENT: the `run` step must execute on an AArch64 (ARMv8-A)
# machine; the generated C program refuses to build elsewhere.
#
# Usage: make check   (from this directory, or
#        make -C compiler check-armv8a-semantics from the repo root)

CC     ?= cc
CFLAGS ?= -O1 -Wall
GEN    := gen
EXE    := $(GEN)/armv8a_hw_semantics_test

.PHONY: check clean

check: $(EXE)
	./$(EXE)

$(EXE): $(GEN)/armv8a_hw_semantics_test.c
	$(CC) $(CFLAGS) -o $@ $<

$(GEN)/armv8a_hw_semantics_test.c: gen_armv8a_hw_semantics.ml dune FORCE
	dune build ./gen_armv8a_hw_semantics.exe
	mkdir -p $(GEN)
	dune exec ./gen_armv8a_hw_semantics.exe > $@

.PHONY: FORCE
FORCE:

clean:
	rm -rf $(GEN)
