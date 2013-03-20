import why3 "bool" "Bool"
  op "xorb" as "^^".

lemma xorb_spec: forall b1 b2,
  b1 ^^ b2 <=> b1 = !b2.

op xorb(b0 b1:bool):bool =  b0 ^^ b1.

require import Real.
require import Distr.

(* Uniform distribution on booleans *)
theory Dbool.
  cnst dbool: bool distr.

  axiom supp_def: forall (b:bool),
    in_supp b dbool.

  axiom mu_def: forall (P:bool cPred), 
      mu dbool P =
       (1%r/2%r) * caract P true 
     + (1%r/2%r) * caract P false.
  
  axiom mu_x_def: forall (b:bool),
    mu_x dbool b = 1%r/2%r.

  lemma mu_weight: mu_weight dbool = 1%r
  proof.
  cut H: (caract cPtrue true = 1%r /\ caract cPtrue false = 1%r);
    trivial.
  save.
end Dbool.
