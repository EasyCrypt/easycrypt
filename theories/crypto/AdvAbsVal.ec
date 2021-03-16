(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require import Real.

module type Adv = {
  proc main () : bool
}.

module Neg_main (A:Adv) = {
  proc main () : bool = {
    var b : bool;
    b <@ A.main ();
    return !b;
  }
}.

equiv Neg_A (A<:Adv) :
  Neg_main(A).main ~ A.main : ={glob A} ==> res{1} = !res{2}.
proof.
proc *; inline{1} Neg_main(A).main.
by wp; call (: true).
qed.

lemma Neg_A_Pr (A<:Adv) &m:
  Pr[Neg_main(A).main() @ &m : res] = Pr[A.main() @ &m : !res].
proof. by byequiv (Neg_A A). qed.

lemma Neg_A_Pr_minus (A<:Adv) &m:
  islossless A.main =>
  Pr[Neg_main(A).main() @ &m : res] = 1%r - Pr[A.main() @ &m : res].
proof.
move=> Hl; rewrite (Neg_A_Pr A &m); rewrite Pr[mu_not]; congr => //.
by byphoare Hl.
qed.

lemma abs_val (P:real -> bool):
  (forall &m (A <: Adv), P (Pr[A.main() @ &m : res] - 1%r/2%r)) =>
  forall &m (A <: Adv), islossless A.main =>
      P (`|Pr[A.main() @ &m : res] - 1%r/2%r|).
proof.
move=> HP &m A Hl.
case (Pr[A.main() @ &m : res] <= 1%r / 2%r)=> Hle.
+ by move: (HP &m (Neg_main(A))); rewrite (Neg_A_Pr_minus A &m) /#.
by move: (HP &m A)=> /#.
qed.
