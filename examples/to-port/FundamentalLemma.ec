require import Real Distr StdOrder.
(*---*) import RealOrder.

op max (x y:real) = if x <= y then y else x.

type t.

(* We want the bad event to be defined on both sides, *
 * so we assume that all the variables that are used  *
 * to define victory conditions and bad events are    *
 * stored in a separate module. (Note: the empty      *
 * signature could be instantiated with anything,     *
 * including the concrete experiment themselves       *
 * if their glob types match.)                        *)
module type Mem = { }.

module type Exp = {
  proc main(): t
}.

lemma Pr_split (G <: Exp) (Mem <: Mem) (A: (glob Mem) -> t -> bool) (F: (glob Mem) -> t -> bool) &m:
  Pr[G.main() @ &m: A (glob Mem) res /\ F (glob Mem) res]
  + Pr[G.main() @ &m: A (glob Mem) res /\ !F (glob Mem) res]
  = Pr[G.main() @ &m: A (glob Mem) res].
proof.
  cut: Pr[G.main() @ &m: A (glob Mem) res /\ F (glob Mem) res]
       + Pr[G.main() @ &m: A (glob Mem) res /\ !F (glob Mem) res]
       = Pr[G.main() @ &m: (A (glob Mem) res /\ F (glob Mem) res) \/ (A (glob Mem) res /\ !F (glob Mem) res)]
    by (rewrite Pr [mu_disjoint]; smt).
  cut ->: Pr[G.main() @ &m: (A (glob Mem) res /\ F (glob Mem) res) \/ (A (glob Mem) res /\ ! F (glob Mem) res)]
          = Pr[G.main() @ &m: A (glob Mem) res]
    by (rewrite Pr [mu_eq]; smt).
  by move => <-.
qed.

lemma FundamentalLemma (G1 <: Exp) (G2 <: Exp) (Mem <: Mem)
                       (A: (glob Mem) -> t -> bool) (B: (glob Mem) -> t -> bool)
                       (F: (glob Mem) -> t -> bool) &m:
  Pr[G1.main() @ &m: A (glob Mem) res /\ !F (glob Mem) res] =
    Pr[G2.main() @ &m: B (glob Mem) res /\ !F (glob Mem) res] =>
  `|Pr[G1.main() @ &m: A (glob Mem) res] - Pr[G2.main() @ &m: B (glob Mem) res]|
  <= max Pr[G1.main() @ &m: F (glob Mem) res] Pr[G2.main() @ &m: F (glob Mem) res].
proof.
  rewrite -(Pr_split G1 Mem A F &m) -(Pr_split G2 Mem B F &m)=> ->.
  cut ->: forall (x y z:real), x + y - (z + y) = x - z by smt.
  apply (ler_trans (max Pr[G1.main() @ &m: A (glob Mem) res /\ F (glob Mem) res]
                   Pr[G2.main() @ &m: B (glob Mem) res /\ F (glob Mem) res]));
    first smt full.
  cut H: forall (x y x' y':real), x <= x' => y <= y' => max x y <= max x' y' by smt.
  apply H.
    rewrite -(Pr_split G1 Mem F A &m) andC; smt.
    rewrite -(Pr_split G2 Mem F B &m) andC; smt.
qed.
