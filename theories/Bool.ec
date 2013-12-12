op (^^) (b1 b2:bool) = b1 = !b2.

lemma nosmt xor_false b: b ^^ false = b
by [].

lemma nosmt xor_true b: b ^^ true = !b
by [].

lemma nosmt xorA b1 b2 b3: (b1 ^^ b2) ^^ b3 = b1 ^^ (b2 ^^ b3)
by [].

lemma nosmt xorC b1 b2: b1 ^^ b2 = b2 ^^ b1
by [].

lemma nosmt xorK b: b ^^ b = false
by [].

require import Real.
require import Distr.

(** Uniform distribution on booleans *)
theory Dbool.
  op dbool: bool distr.

  axiom mu_def (p:bool -> bool):
    mu dbool p = (1%r / 2%r) * charfun p true + (1%r / 2%r) * charfun p false.
 
  lemma supp_def (b:bool): in_supp b dbool.
  proof strict.
  by rewrite /in_supp /mu_x mu_def /charfun; smt.
  qed.
  
  lemma mu_x_def (b:bool): mu_x dbool b = 1%r / 2%r.
  proof strict.
  by rewrite /mu_x mu_def /charfun; smt.
  qed.

  lemma lossless: weight dbool = 1%r by [].
end Dbool.
