op fst (p:'a * 'b): 'a = 
  let (a,b) = p in a.

op snd (p:'a * 'b): 'b = 
  let (a,b) = p in b.

require import Real.
require import Distr.

(* Product distribution *)
theory Dprod.
  op dprod: 'a distr -> 'b distr -> ('a * 'b) distr.
  
  axiom supp_def: forall (d1:'a distr) (d2:'b distr) p, 
    in_supp p (dprod d1 d2) <=>
    in_supp (fst p) d1 /\ in_supp (snd p) d2.

  axiom mu_x_def: forall (d1:'a distr) (d2:'b distr) p, 
      mu_x (dprod d1 d2) p = mu_x d1 (fst p) * mu_x d2 (snd p).

  axiom weight_def: forall (d1:'a distr) (d2:'b distr), 
     weight (dprod d1 d2) = weight d1 * weight d2.
end Dprod.
