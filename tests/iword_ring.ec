(* -------------------------------------------------------------------- *)
(* The generic [Ring.BoolRing] instance over [word<:n+1>] (registered in
   [IWord]) lets the [ring] tactic fire on any manifestly-nonzero word
   width, without a per-width clone: symbolic ([word<:k+1>]) and concrete
   ([word<:8>], [word<:64>]) alike.  Instance resolution unifies the goal
   width against [?i+1], which succeeds exactly when the width is provably
   positive and refuses an arbitrary (possibly zero) [word<:m>]. *)
require import AllCore Bool Ring.
require import IArray IWord.

(* Symbolic width. *)
lemma addwA {k} (a b c : word<:k+1>) : a +^ (b +^ c) = (a +^ b) +^ c by ring.
lemma andwC {k} (a b   : word<:k+1>) : andw a b = andw b a by ring.
lemma andwDl {k} (a b c : word<:k+1>) :
  andw a (b +^ c) = andw a b +^ andw a c by ring.

(* Concrete widths. *)
lemma at8  (a b : word<:8>)  : a +^ b = b +^ a by ring.
lemma at64 (a b : word<:64>) : andw a (andw b a) = andw (andw a b) a by ring.

(* ------------------------------------------------------------------ *)
(* The NAMED arithmetic instance: [ring [warith]] selects ℤ/2ⁿ even
   though the boolean instance is registered first on the same
   carrier (review finding: the arithmetic structure was unreachable). *)

lemma arith_comm8 (a b : word<:8>) : a + b = b + a.
proof. by ring [warith]. qed.

lemma arith_distr8 (a b c : word<:8>) : a * (b + c) = a * b + a * c.
proof. by ring [warith]. qed.

lemma arith_symb {k} (a b : word<:k+1>) : a + b = b + a.
proof. by ring [warith]. qed.

(* bare [ring] still selects the boolean structure *)
lemma bool_still8 (a b : word<:8>) : a +^ b = b +^ a.
proof. by ring. qed.
