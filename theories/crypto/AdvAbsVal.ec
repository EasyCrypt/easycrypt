(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
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
    b = A.main ();
    return !b;
  }
}.

equiv Neg_A (A<:Adv) :
   Neg_main(A).main ~ A.main : ={glob A} ==> res{1} = !res{2}.
proof -strict.
 proc *;inline{1} Neg_main(A).main.
 by wp;call (_:true).
qed.

lemma Neg_A_Pr (A<:Adv) &m:
   Pr[Neg_main(A).main() @ &m : res] = Pr[A.main() @ &m : !res].
proof -strict.
  byequiv (Neg_A A) => //.
qed.

lemma Neg_A_Pr_minus (A<:Adv) &m:
   islossless A.main =>
   Pr[Neg_main(A).main() @ &m : res] = 1%r - Pr[A.main() @ &m : res].
proof -strict.
  move=> Hl; rewrite (Neg_A_Pr A &m); rewrite Pr[mu_not]; congr => //.
  by byphoare Hl.
qed.

lemma abs_val :
    forall (P:real -> bool),
    (forall &m (A<:Adv), P (Pr[A.main() @ &m : res] - 1%r/2%r)) =>
    forall &m (A<:Adv), islossless A.main =>
      P (`|Pr[A.main() @ &m : res] - 1%r/2%r| ).
proof.
  move=> P HP &m A Hl.
  case (Pr[A.main() @ &m : res] <= 1%r / 2%r) => Hle.
    cut h1 := HP &m (Neg_main(A)).
    cut h2 := Neg_A_Pr_minus A &m _; first by trivial.
    smt.
  by cut h := HP &m A; smt.
qed.
