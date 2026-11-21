(* ==================================================================== *)
require import AllCore IntDiv.
require Subtype.
require MaxBigop.

(* ==================================================================== *)
(* Non-negative integers as a subtype of [int].                          *)
(*                                                                      *)
(* This type exists so that constructions requiring a globally-minimal  *)
(* element (e.g. the identity of a max-monoid) can sit on something    *)
(* simpler than [int].  The traditional name "nat" is avoided because  *)
(* of overload with OCaml's primitive [nat] and because it conflates   *)
(* "natural numbers" (sometimes 0+, sometimes 1+) with the more         *)
(* specific "non-negative integers" we mean here.                       *)
(* ==================================================================== *)

(* -------------------------------------------------------------------- *)
subtype nneg = { x : int | 0 <= x }.
realize inhabited by exists 0.

(* -------------------------------------------------------------------- *)
(* Conversions and constants. *)

(* val : nneg -> int    (canonical injection) *)
(* insubd : int -> nneg (saturates negatives to witness, but we use     *)
(*  ofint below for a saturating-to-zero version)                       *)

op ofint (x : int) : nneg = insubd (max 0 x).

op zero : nneg = ofint 0.
op one  : nneg = ofint 1.

op (<=) (x y : nneg) : bool = val x <= val y.

(* -------------------------------------------------------------------- *)
lemma ge0_val (x : nneg) : 0 <= val x.
proof. exact valP. qed.

lemma valK_pos (x : int) : 0 <= x => val (ofint x) = x.
proof.
move=> h; rewrite /ofint.
have -> : max 0 x = x by smt().
by rewrite insubdK.
qed.

lemma val_zero : val zero = 0.
proof. by rewrite /zero valK_pos. qed.

lemma val_one : val one = 1.
proof. by rewrite /one valK_pos. qed.

(* -------------------------------------------------------------------- *)
(* Order properties. *)

lemma le_refl (x : nneg) : x <= x.
proof. by rewrite /(<=). qed.

lemma le_trans (y x z : nneg) : x <= y => y <= z => x <= z.
proof. by rewrite /(<=); smt(). qed.

lemma le_anti (x y : nneg) : x <= y => y <= x => x = y.
proof. by rewrite /(<=); smt(val_inj). qed.

lemma le_total (x y : nneg) : x <= y \/ y <= x.
proof. by rewrite /(<=); smt(). qed.

lemma zero_le (x : nneg) : zero <= x.
proof. by rewrite /(<=) val_zero ge0_val. qed.

(* ==================================================================== *)
(* Big-fold of [max] over [nneg].                                        *)
(* ==================================================================== *)
clone import MaxBigop as BMaxN with
  type t       <- nneg,
    op (<=)    <- (<=),
    op bot     <- zero
  proof le_refl  by exact le_refl,
        le_trans by exact le_trans,
        le_anti  by exact le_anti,
        le_total by exact le_total,
        bot_le   by exact zero_le.