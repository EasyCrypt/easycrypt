(* ==================================================================== *)
(* [circuit] over words of several sizes.                               *)
(*                                                                       *)
(* Each width is a separate [bind bitstring]-bound type with its own     *)
(* operators (suffixed by the width to keep them distinct). Size-        *)
(* changing operators (concat, zextend, truncate) are multi-type         *)
(* [bind op]s relating two (or three) widths.                            *)
(*                                                                       *)
(* As elsewhere, the [bind] side conditions are admitted; the tactic     *)
(* invocations are real and run.                                         *)
(* ==================================================================== *)
require import AllCore List QFABV IntDiv.

(* -------------------------------------------------------------------- *)
(* An 8-bit word. *)
type W8.
op to_bits8 : W8 -> bool list.   op from_bits8 : bool list -> W8.
op of_int8  : int -> W8.         op to_uint8 : W8 -> int.
op to_sint8 : W8 -> int.

bind bitstring to_bits8 from_bits8 to_uint8 to_sint8 of_int8 W8 8.
realize gt0_size by admit.  realize tolistP by admit.  realize oflistP by admit.
realize touintP by admit.   realize tosintP by admit.  realize ofintP by admit.
realize size_tolist by admit.

op xor8 : W8 -> W8 -> W8.    bind op W8 xor8 "xor".  realize bvxorP by admit.

(* -------------------------------------------------------------------- *)
(* A 16-bit word. *)
type W16.
op to_bits16 : W16 -> bool list.  op from_bits16 : bool list -> W16.
op of_int16  : int -> W16.        op to_uint16 : W16 -> int.
op to_sint16 : W16 -> int.

bind bitstring to_bits16 from_bits16 to_uint16 to_sint16 of_int16 W16 16.
realize gt0_size by admit.  realize tolistP by admit.  realize oflistP by admit.
realize touintP by admit.   realize tosintP by admit.  realize ofintP by admit.
realize size_tolist by admit.

op xor16 : W16 -> W16 -> W16. bind op W16 xor16 "xor". realize bvxorP by admit.
op add16 : W16 -> W16 -> W16. bind op W16 add16 "add". realize bvaddP by admit.

(* -------------------------------------------------------------------- *)
(* A 32-bit word. *)
type W32.
op to_bits32 : W32 -> bool list.  op from_bits32 : bool list -> W32.
op of_int32  : int -> W32.        op to_uint32 : W32 -> int.
op to_sint32 : W32 -> int.

bind bitstring to_bits32 from_bits32 to_uint32 to_sint32 of_int32 W32 32.
realize gt0_size by admit.  realize tolistP by admit.  realize oflistP by admit.
realize touintP by admit.   realize tosintP by admit.  realize ofintP by admit.
realize size_tolist by admit.

op xor32 : W32 -> W32 -> W32. bind op W32 xor32 "xor". realize bvxorP by admit.
op add32 : W32 -> W32 -> W32. bind op W32 add32 "add". realize bvaddP by admit.

(* ==================================================================== *)
(* Same-size reasoning at each width                                    *)
(* ==================================================================== *)

lemma xor_comm8  (a b : W8)  : xor8  a b = xor8  b a by circuit.
lemma xor_comm16 (a b : W16) : xor16 a b = xor16 b a by circuit.
lemma xor_comm32 (a b : W32) : xor32 a b = xor32 b a by circuit.

(* add is commutative at 32 bits. *)
lemma add_comm32 (a b : W32) : add32 a b = add32 b a by circuit.

(* A slightly deeper 16-bit goal. *)
lemma xor_rot16 (a b c : W16) :
  xor16 (xor16 a b) c = xor16 (xor16 c a) b by circuit.

(* ==================================================================== *)
(* concat : combine two W8s into a W16                                  *)
(* ==================================================================== *)

op concat8 : W8 -> W8 -> W16.
bind op [W8 & W8 & W16] concat8 "concat".
realize eq_size   by done.   (* 8 + 8 = 16 *)
realize bvconcatP by admit.

(* ==================================================================== *)
(* zextend / truncate : move between W8 and W16                         *)
(* ==================================================================== *)

op zext : W8 -> W16.
bind op [W8 & W16] zext "zextend".
realize le_size     by done.   (* 8 <= 16 *)
realize bvzextendP  by admit.

op trunc : W16 -> W8.
bind op [W16 & W8] trunc "truncate".
realize le_size     by done.   (* 8 <= 16 *)
realize bvtruncateP by admit.

(* Truncating a zero-extended word returns the original. *)
lemma trunc_zext (a : W8) : trunc (zext a) = a by circuit.

(* ==================================================================== *)
(* A small program mixing widths                                        *)
(* ==================================================================== *)

module M = {
  proc widen_xor (a b : W8) : W16 = {
    var r : W16;
    r <- zext (xor8 a b);
    return r;
  }
}.

lemma hl_widen_xor (a_ b_ : W8) :
  hoare[M.widen_xor : a_ = a /\ b_ = b ==> res = zext (xor8 a_ b_)].
proof. proc; circuit. qed.
