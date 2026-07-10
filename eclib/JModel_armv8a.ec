(* -------------------------------------------------------------------- *)
(* EasyCrypt model of the Jasmin ARMv8-A (AArch64) instructions.
   General-purpose registers are modeled at their full 64-bit width. *)
require import AllCore List Bool IntDiv.
require export JModel_common JArray JWord_array JMemory JLeakage Jslh.


abbrev ptr_modulus = 2^64.

(* -------------------------------------------------------------------- *)
op nzcv (r: W64.t) (u s: int) : bool * bool * bool * bool =
  (W64.msb r,
   r = W64.zero,
   to_uint r <> u,
   to_sint r <> s).

abbrev with_nzcv r u s =
  let (n, z, c, v) = nzcv r u s in
  (n, z, c, v, r).

(* Flags of the flag-setting logical instructions:
   N and Z from the result, C and V cleared. *)
abbrev with_nzcv_log (r: W64.t) =
  (W64.msb r, r = W64.zero, false, false, r).

(* -------------------------------------------------------------------- *)
(* Arithmetic. *)

op ADD (x y: W64.t) : W64.t = x + y.
op ADDS (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv (x + y) (to_uint x + to_uint y) (to_sint x + to_sint y).

op ADC (x y: W64.t) (c: bool) : W64.t =
  x + y + (if c then W64.one else W64.zero).
op ADCS (x y: W64.t) (c: bool) : bool * bool * bool * bool * W64.t =
  let r = ADC x y c in
  with_nzcv r (to_uint x + to_uint y + b2i c) (to_sint x + to_sint y + b2i c).

op SUB (x y: W64.t) : W64.t = x - y.
op SUBS (x y: W64.t) : bool * bool * bool * bool * W64.t =
  ADCS x (invw y) true.

op SBC (x y: W64.t) (c: bool) : W64.t = ADC x (invw y) c.
op SBCS (x y: W64.t) (c: bool) : bool * bool * bool * bool * W64.t =
  ADCS x (invw y) c.

op NEG (x: W64.t) : W64.t = invw x + W64.one.

op MUL (x y: W64.t) : W64.t = x * y.
op MADD (x y a: W64.t) : W64.t = a + x * y.
op MSUB (x y a: W64.t) : W64.t = a - x * y.

op SDIV (x y: W64.t) : W64.t = x \sdiv y.
op UDIV (x y: W64.t) : W64.t = x \udiv y.

op UMULL (x y: W32.t) : W64.t = zeroextu64 x * zeroextu64 y.
op SMULL (x y: W32.t) : W64.t = sigextu64 x * sigextu64 y.
op UMADDL (x y: W32.t) (a: W64.t) : W64.t = a + zeroextu64 x * zeroextu64 y.
op SMADDL (x y: W32.t) (a: W64.t) : W64.t = a + sigextu64 x * sigextu64 y.

op UMULH (x y: W64.t) : W64.t =
  W64.of_int ((to_uint x * to_uint y) %/ 2^64).
op SMULH (x y: W64.t) : W64.t =
  W64.of_int ((to_sint x * to_sint y) %/ 2^64).

(* -------------------------------------------------------------------- *)
(* Logical. *)

op AND (x y: W64.t) : W64.t = andw x y.
op ANDS (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv_log (andw x y).

op BIC (x y: W64.t) : W64.t = andw x (invw y).
op BICS (x y: W64.t) : bool * bool * bool * bool * W64.t =
  with_nzcv_log (andw x (invw y)).

op ORR (x y: W64.t) : W64.t = orw x y.
op EOR (x y: W64.t) : W64.t = x +^ y.
op MVN (x: W64.t) : W64.t = invw x.

(* -------------------------------------------------------------------- *)
(* Shifts. The shift amount is taken modulo the register size. *)

op ASR (x: W64.t) (sham: W8.t) : W64.t = x `|>>` W8.of_int (to_uint sham %% 64).
op LSL (x: W64.t) (sham: W8.t) : W64.t = x `<<` W8.of_int (to_uint sham %% 64).
op LSR (x: W64.t) (sham: W8.t) : W64.t = x `>>` W8.of_int (to_uint sham %% 64).
op ROR (x: W64.t) (sham: W8.t) : W64.t = x `|>>>` (to_uint sham %% 64).

(* -------------------------------------------------------------------- *)
(* Bit field operations. *)

op BFC (x: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W64.init (fun i => if lsbit <= i <= msbit then false else x.[i]).

op BFI (x y: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let msbit = lsbit + to_uint width - 1 in
  W64.init (fun i => if lsbit <= i <= msbit then y.[i - lsbit] else x.[i]).

op BFXIL (x y: W64.t) (lsb width: W8.t) : W64.t =
  let lsbit = to_uint lsb in
  let nbits = to_uint width in
  W64.init (fun i => if i < nbits then y.[i + lsbit] else x.[i]).

op UBFX (x: W64.t) (lsb width: W8.t) : W64.t =
  (x `<<` W8.of_int (64 - to_uint width - to_uint lsb))
    `>>` W8.of_int (64 - to_uint width).

op SBFX (x: W64.t) (lsb width: W8.t) : W64.t =
  (x `<<` W8.of_int (64 - to_uint width - to_uint lsb))
    `|>>` W8.of_int (64 - to_uint width).

op EXTR (x y: W64.t) (lsb: W8.t) : W64.t =
  let l = to_uint lsb %% 64 in
  if l = 0 then y else orw (y `>>` W8.of_int l) (x `<<` W8.of_int (64 - l)).

(* -------------------------------------------------------------------- *)
(* Moves. *)

op MOV (x: W64.t) : W64.t = x.

op MOVZ (imm: W16.t) (sh: W8.t) : W64.t =
  zeroextu64 imm `<<` sh.

op MOVN (imm: W16.t) (sh: W8.t) : W64.t =
  invw (zeroextu64 imm `<<` sh).

op MOVK (old: W64.t) (imm: W16.t) (sh: W8.t) : W64.t =
  let mask = zeroextu64 (W16.of_int (-1)) `<<` sh in
  orw (zeroextu64 imm `<<` sh) (andw old (invw mask)).

op ADR (x: W64.t) : W64.t = x.

(* -------------------------------------------------------------------- *)
(* Extensions. *)

op SXTB (x: W8.t)  : W64.t = W64.of_int (W8.to_sint x).
op SXTH (x: W16.t) : W64.t = W64.of_int (W16.to_sint x).
op SXTW (x: W32.t) : W64.t = W64.of_int (W32.to_sint x).
op UXTB (x: W8.t)  : W64.t = W64.of_int (W8.to_uint x).
op UXTH (x: W16.t) : W64.t = W64.of_int (W16.to_uint x).
op UXTW (x: W32.t) : W64.t = W64.of_int (W32.to_uint x).

(* -------------------------------------------------------------------- *)
(* Bit manipulation. *)

op RBIT (x: W64.t) : W64.t =
  W64.init (fun i => x.[63 - i]).

op REV (x: W64.t) : W64.t =
  W64.init (fun i => x.[8 * (7 - i %/ 8) + i %% 8]).

op REV16 (x: W64.t) : W64.t =
  W64.init (fun i => x.[16 * (i %/ 16) + 8 * (1 - (i %% 16) %/ 8) + i %% 8]).

op REV32 (x: W64.t) : W64.t =
  W64.init (fun i => x.[32 * (i %/ 32) + 8 * (3 - (i %% 32) %/ 8) + i %% 8]).

op CLZ (x: W64.t) : W64.t =
  W64.of_int (lzcnt (rev (w2bits x))).

op CLS (x: W64.t) : W64.t =
  let t = andw ((x `>>` W8.one) +^ x) (W64.of_int (2^63 - 1)) in
  W64.of_int (lzcnt (rev (w2bits t)) - 1).

(* -------------------------------------------------------------------- *)
(* Comparisons. *)

(* CMP, CMN and TST are the flag-only aliases of SUBS, ADDS and ANDS. *)
op CMP (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = SUBS x y in (n, z, c, v).

op CMN (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = ADDS x y in (n, z, c, v).

op TST (x y: W64.t) : bool * bool * bool * bool =
  let (n, z, c, v, _) = ANDS x y in (n, z, c, v).

(* -------------------------------------------------------------------- *)
(* Conditional selection. *)

op CSEL  (x y: W64.t) (b: bool) : W64.t = if b then x else y.
op CSINC (x y: W64.t) (b: bool) : W64.t = if b then x else y + W64.one.
op CSINV (x y: W64.t) (b: bool) : W64.t = if b then x else invw y.
op CSNEG (x y: W64.t) (b: bool) : W64.t = if b then x else invw y + W64.one.
op CSET  (b: bool) : W64.t = if b then W64.one else W64.zero.
op CSETM (b: bool) : W64.t = if b then W64.of_int (-1) else W64.zero.

(* -------------------------------------------------------------------- *)
(* Loads and stores. The memory access itself is part of the Jasmin
   semantics; these operators only extend the transferred value. *)

op LDR (x: W64.t) : W64.t = x.
op LDRB (x: W8.t) : W64.t = W64.of_int (W8.to_uint x).
op LDRH (x: W16.t) : W64.t = W64.of_int (W16.to_uint x).
op LDRSB (x: W8.t) : W64.t = W64.of_int (W8.to_sint x).
op LDRSH (x: W16.t) : W64.t = W64.of_int (W16.to_sint x).
op LDRSW (x: W32.t) : W64.t = W64.of_int (W32.to_sint x).

op STR (x: W64.t) : W64.t = x.
op STRB (x: W8.t) : W8.t = x.
op STRH (x: W16.t) : W16.t = x.
