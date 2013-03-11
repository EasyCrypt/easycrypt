(* abelian groups of prime order *)
require import prime_field.

type group.
cnst g : group. (* the generator *)

op [*] : (group, group) -> group.   (* multiplication of group elements *)
op [^] : (group, gf_q) -> group.    (* exponentiation *)
op log : group -> gf_q.             (* discrete logarithm *)

axiom group_pow_add : forall (x y : gf_q), g ^ x * g ^ y = g ^ (x + y).

axiom group_pow_mult : forall (x y : gf_q),  (g ^ x) ^ y = g ^ (x * y).

axiom group_log_pow : forall (a : group), g ^ log(a) = a.

axiom group_pow_log : forall (x : gf_q), log(g^x) = x.
