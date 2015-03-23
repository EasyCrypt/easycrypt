(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

(* cyclic groups of prime order *)
require import Prime_field.
require import Real.
require import Distr.

type group.
const g:group. (* the generator *)

op ( * ): group -> group -> group.   (* multiplication of group elements *)
op ( / ): group -> group -> group.   (* division *)
op ( ^ ): group -> gf_q -> group.    (* exponentiation *)
op log:group -> gf_q.                (* discrete logarithm *)

axiom div_def (a b:group): g^(log a - log b) = a / b.

axiom group_pow_add (x y:gf_q):
  g ^ x * g ^ y = g ^ (x + y).

axiom group_pow_mult (x y:gf_q):
  (g ^ x) ^ y = g ^ (x * y).

axiom group_log_pow (a:group):
  g ^ (log a) = a.

axiom group_pow_log (x:gf_q):
  log (g ^ x) = x.

theory Dgroup.
  op dgroup: group distr.

  axiom supp_def: forall (s:group),
    in_supp s dgroup.

  axiom mu_x_def_in: forall (s:group),
    mu_x dgroup s = 1%r/q%r.

  axiom lossless: weight dgroup = 1%r.
end Dgroup.
