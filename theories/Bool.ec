import why3 "bool" "Bool"
  op "xorb" as "^^".

op xorb(b0:bool, b1:bool):bool = b0 ^^ b1.

lemma xorb_nilpotent: forall b,
  b ^^ b = false.

lemma xorb_commutative: forall b0 b1,
  b0 ^^ b1 = b1 ^^ b0.

lemma xorb_zero: forall b,
  b ^^ false = b.

lemma xorb_not: forall b,
  b ^^ true = !b.

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

  lemma mu_weight: mu_weight dbool = 1%r.
end Dbool.
