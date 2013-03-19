(* cyclic groups of prime order *)
require import Prime_field.

type group.
cnst g:group. (* the generator *)

op [*]:(group, group) -> group.   (* multiplication of group elements *)
op [^]:(group, gf_q) -> group.    (* exponentiation *)
op log:group -> gf_q.             (* discrete logarithm *)

op [/] (a b:group): group = g^(log a - log b).

axiom group_pow_add: forall (x y:gf_q),
  g ^ x * g ^ y = g ^ (x + y).

axiom group_pow_mult: forall (x y:gf_q),
  (g ^ x) ^ y = g ^ (x * y).

axiom group_log_pow: forall (a:group),
  g ^ (log a) = a.

axiom group_pow_log: forall (x:gf_q),
  log (g ^ x) = x.


(* tests 

lemma a: forall (a b : gf_q), (g^a)^b = (g^b)^a.

lemma b: forall (a : group, x : gf_q), (g^(log(a) + x - x)) / a = g^gf_q0.
*)