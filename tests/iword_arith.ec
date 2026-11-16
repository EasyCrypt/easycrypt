(* -------------------------------------------------------------------- *)
(* Tier-1 machine-word surface on top of [IWord]: bitwise [orw], the
   arithmetic (ℤ/2ⁿ) ring via [to_uint] laws, unsigned/signed
   comparisons, and shifts/rotates (as bit reindexings). *)
require import AllCore IntDiv IArray IWord.

(* Bitwise OR. *)
lemma orwC_ {k} (a b : word<:k>) : orw a b = orw b a by apply orwC.

(* Arithmetic: reason through [to_uint] (the machine-word idiom). *)
lemma addC_ {k} (a b : word<:k>) : to_uint (a + b) = to_uint (b + a).
proof. by rewrite !to_uintD addzC. qed.

lemma mulC_ {k} (a b : word<:k>) : to_uint (a * b) = to_uint (b * a).
proof. by rewrite !to_uintM mulzC. qed.

(* Comparisons. *)
lemma uleNgt_ {k} (a b : word<:k>) : (a \ule b) = !(b \ult a) by apply uleNgt.
lemma sltNge_ {k} (a b : word<:k>) : (a \slt b) = !(b \sle a) by apply sltNge.

(* Shifts / rotates as bit reindexings. *)
lemma shr_ {k} (x : word<:k>) i j : 0 <= j < k => (x `>>>` i).[j] = x.[j + i]
  by apply shrwE.
lemma rol_ {k} (x : word<:k>) i j : 0 <= j < k => (rol x i).[j] = x.[(j - i) %% k]
  by apply rolwE.

(* Shift <-> arithmetic (unsigned division / truncated multiplication). *)
lemma shr_uint {k} (x : word<:k>) i :
  0 <= i => to_uint (x `>>>` i) = to_uint x %/ 2 ^ i by apply to_uint_shr.
lemma shl_uint {k} (x : word<:k>) i :
  0 <= i => to_uint (x `<<<` i) = (to_uint x * 2 ^ i) %% 2 ^ k
  by apply to_uint_shl.

(* The underlying pure-integer bit-shift lemmas. *)
lemma bitM {k} (x j i : int) : 0 <= i => 0 <= j < k =>
  int_bit[:k] (x * 2 ^ i) j = (0 <= j - i < k /\ int_bit[:k] x (j - i))
  by apply int_bitMP.

(* ------------------------------------------------------------------ *)
(* The [expr]/[ofint] slots: exponents and literals go through the
   instance's own operators, in the theory's vocabulary. *)
lemma warith_exp {k} (x : word<:k+1>) :
  wexp x 2 = x * x.
proof. by ring [warith]. qed.

lemma warith_ofint {k} (x : word<:k+1>) :
  x * of_int 2 = x + x.
proof. by ring [warith]. qed.

lemma warith_exp8 (x y : word<:8>) :
  wexp (x + y) 2 = wexp x 2 + x * y + x * y + wexp y 2.
proof. by ring [warith]. qed.

(* ------------------------------------------------------------------ *)
(* The instance is FAMILY-WIDE: no positivity requirement.  It fires
   at a bare symbolic width (previously refused: [word<:m>] could be
   the trivial [word<:0>]) and at width 0 itself (ring instances do
   not require [oner_neq0]). *)
lemma warith_bare {m} (x y z : word<:m>) :
  x * (y + z) = z * x + y * x.
proof. by ring [warith]. qed.

lemma warith_zero (x y : word<:0>) :
  x * y + y = y * (x + of_int 1).
proof. by ring [warith]. qed.
