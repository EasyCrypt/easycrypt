(* Definitions of indexed operators reach the provers: an indexed op
   with a plain body is exported as a standard Why3 definition, with
   one bound [int] variable per idxvar (conservative, so no [0 <= i]
   guard is needed).  Before, every indexed op was opaque to smt and
   definitional goals were silently unprovable. *)

require import AllCore.

type {n} vec.

op sz {n} (v : vec<:n>) : int.

(* the body uses the idxvar BOTH through an index position (sz's
   index argument) and as an int term *)
op szp {n} (v : vec<:n>) : int = sz v + n.

lemma t_symbolic {k} (v : vec<:k>) : szp v = sz v + k.
proof. smt(). qed.

lemma t_concrete (v : vec<:5>) : szp v = sz v + 5.
proof. smt(). qed.

(* predicates too *)
pred low {n} (v : vec<:n>) = sz v <= n.

lemma t_pred {k} (v : vec<:k>) : sz v <= k => low v.
proof. smt(). qed.

(* an indexed op used at a shifted width *)
lemma t_shift {k} (v : vec<:k+1>) : szp v = sz v + (k + 1).
proof. smt(). qed.

(* matchfix over an indexed datatype: stays opaque, and the datatype
   itself is not exported -- the goal punts and smt fails cleanly
   (no anomaly) *)
type {n} 'a ivec = [ INil | ICons of 'a & 'a ivec<:n> ].

op hd {n} (d : int) (xs : int ivec<:n>) : int =
  with xs = INil      => d
  with xs = ICons y _ => y.

lemma t_fix_punts (xs : int ivec<:3>) : hd 0 xs = hd 0 xs.
proof.
fail smt().
by [].
qed.
