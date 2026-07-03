(* -------------------------------------------------------------------- *)
(* A [Ring.BoolRing] instance for a CONCRETE word width.  The bitwise laws
   are proved generically once in [IWord]; a ring/algebra structure, being
   over a single carrier type, must be instantiated per concrete width
   ([word<:n>] is a type family, so a generic clone is not expressible).
   The realizations reuse the generic [IWord] laws, and concrete-width goals
   discharge by SMT via per-index monomorphisation ([/#] in [unitP]). *)

require import AllCore Bool Ring.
require import IArray IWord.

op zerow64 : word<:64>                       = zerow.
op onew64  : word<:64>                       = onew.
op add64   (w1 w2 : word<:64>) : word<:64>   = w1 +^ w2.
op mul64   (w1 w2 : word<:64>) : word<:64>   = andw w1 w2.
op opp64   (w : word<:64>)     : word<:64>   = oppw w.
op inv64   (w : word<:64>)     : word<:64>   = w.
pred unit64 (w : word<:64>)                  = w = onew64.

clone import Ring.BoolRing as W64 with
  type t     <- word<:64>,
  op   zeror <- zerow64,
  op   ( + ) <- add64,
  op   [ - ] <- opp64,
  op   oner  <- onew64,
  op   ( * ) <- mul64,
  op   invr  <- inv64,
  pred unit  <- unit64
proof *.
realize addrA.     proof. by move=> ???; rewrite /add64; apply/xorwA. qed.
realize addrC.     proof. by move=> ??; rewrite /add64; apply/xorwC. qed.
realize add0r.     proof. by move=> ?; rewrite /add64 /zerow64 xorwC; apply/xorw0. qed.
realize addNr.     proof. by move=> ?; rewrite /add64 /opp64 /oppw /zerow64; apply/xorwK. qed.
realize oner_neq0. proof. by rewrite /zerow64 /onew64; apply/onew_neq0. qed.
realize mulrA.     proof. by move=> ???; rewrite /mul64; apply/andwA. qed.
realize mulrC.     proof. by move=> ??; rewrite /mul64; apply/andwC. qed.
realize mul1r.     proof. by move=> ?; rewrite /mul64 /onew64 andwC; apply/andw1. qed.
realize mulrDl.    proof. by move=> ???; rewrite /mul64 /add64; apply/andwDl. qed.
realize unitout.   proof. by move=> x _; rewrite /inv64. qed.
realize mulVr.
proof.
move=> x hx; rewrite /mul64 /inv64 andwK.
by move: hx; rewrite /unit64.
qed.
realize unitP.
proof.
move=> x y; rewrite /unit64 /mul64 -wordP => h.
apply/wordP => i hi; move: (h i hi).
by rewrite andwE onewE hi /#.
qed.
