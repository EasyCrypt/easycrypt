import why3 "bool" "Bool"
  op "xorb" as "^^".

lemma nosmt xor_spec : forall b1 b2, b1 ^^ b2 <=> b1 = !b2
by [].

lemma nosmt xor_false : forall b, b ^^ false = b
by [].

lemma nosmt xor_true : forall b, b ^^ true = !b
by [].

lemma nosmt xor_comm : forall b1 b2, b1 ^^ b2 = b2 ^^ b1
by [].

lemma xor_nilpotent : forall b, b ^^ b = false
by [].

lemma xor_associative : forall b1 b2 b3, (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3)
by [].

require import Real. 
require import Distr.

(** Uniform distribution on booleans *)
theory Dbool.
  op dbool : bool distr.

  axiom mu_def : forall (p:bool cpred), 
    mu dbool p = (1%r / 2%r) * charfun p true + (1%r / 2%r) * charfun p false.
 
  lemma supp_def : forall (b:bool), in_supp b dbool.
  proof.
    intros b; delta in_supp mu_x beta.
    rewrite (mu_def ((=) b)).
    simplify delta;smt.
  qed.
  
  lemma mu_x_def : forall (b:bool), mu_x dbool b = 1%r / 2%r.
  proof.
    intros b.
    simplify mu_x.
    rewrite (mu_def ((=) b)).
    simplify delta; smt.
  qed.

  lemma lossless : weight dbool = 1%r by [].

end Dbool.
