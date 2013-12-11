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
proof. 
 proc *;inline{1} Neg_main(A).main.
 by wp;call (_:true).
qed.

lemma Neg_A_Pr (A<:Adv) &m: 
   Pr[Neg_main(A).main() @ &m : res] = Pr[A.main() @ &m : !res].
proof.
  equiv_deno (Neg_A A) => //.
qed.

lemma Neg_A_Pr_minus (A<:Adv) &m: 
   islossless A.main => 
   Pr[Neg_main(A).main() @ &m : res] = 1%r - Pr[A.main() @ &m : res].
proof.
  intros Hl; rewrite (Neg_A_Pr A &m); rewrite Pr mu_not; congr => //.
  by phoare_deno Hl.
qed.
  
lemma abs_val : 
    forall (P:real -> bool), 
    (forall &m (A<:Adv), P (Pr[A.main() @ &m : res] - 1%r/2%r)) =>
    forall &m (A<:Adv), islossless A.main => 
      P (`|Pr[A.main() @ &m : res] - 1%r/2%r| ).
proof.
 intros P HP &m A Hl.
 case (Pr[A.main() @ &m : res] <= 1%r / 2%r) => Hle.
   cut H  := HP &m (Neg_main(A)).
   cut H1 := Neg_A_Pr_minus A &m _; [trivial | smt].
 cut H := HP &m A;smt.
qed.






    


