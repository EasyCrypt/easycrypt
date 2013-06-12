(* cyclic groups of prime order *)
require import Prime_field.
require import Real.
require import Distr.

type group.
op g:group. (* the generator *)

op ( * ): group -> group -> group.   (* multiplication of group elements *)
op ( ^ ): group -> gf_q -> group.    (* exponentiation *)
op log:group -> gf_q.             (* discrete logarithm *)

op (/) (a b:group): group = g^(log a - log b).

axiom group_pow_add: forall (x y:gf_q),
  g ^ x * g ^ y = g ^ (x + y).

axiom group_pow_mult: forall (x y:gf_q),
  (g ^ x) ^ y = g ^ (x * y).

axiom group_log_pow: forall (a:group),
  g ^ (log a) = a.

axiom group_pow_log: forall (x:gf_q),
  log (g ^ x) = x.


theory Dgroup.
  op dgroup: group distr.

  axiom supp_def: forall (s:group),
    in_supp s dgroup.

  axiom mu_x_def_in: forall (s:group),
    mu_x dgroup s = 1%r/q%r.

  axiom lossless: weight dgroup = 1%r.

end Dgroup.

(* tests 

lemma a: forall (a b : gf_q), (g^a)^b = (g^b)^a.

lemma b: forall (a : group, x : gf_q), (g^(log(a) + x - x)) / a = g^gf_q0.
*)
