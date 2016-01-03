(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

require PrimeField.

clone export PrimeField as FD.

type group.

op g:group. (* the generator *)
op ( * ): group -> group -> group.   (* multiplication of group elements *)
op inv : group -> group.             (* inverse of the multiplication *) 
op ( / ): group -> group -> group.   (* division *)
op ( ^ ): group -> t -> group.       (* exponentiation *)
op log  : group -> t.                (* discrete logarithm *)
op g1 = g ^ F.zero.

axiom gpow_log (a:group): g ^ (log a) = a.
axiom log_gpow x : log (g ^ x) = x.

lemma nosmt log_bij x y: x = y <=> log x = log y by smt full.
lemma nosmt pow_bij (x y:F.t): x = y <=> g^x =g^y by [].


axiom inv_def (a:group): inv a = g ^ (-log a).
axiom div_def (a b:group): g^(log a - log b) = a / b.

axiom mul_pow g (x y:t): g ^ x * g ^ y = g ^ (x + y).

axiom pow_pow g (x y:t): (g ^ x) ^ y = g ^ (x * y).

lemma nosmt log_pow (g1:group) x: log (g1 ^ x) = log g1 * x by [].

lemma nosmt log_mul (g1 g2:group): log (g1 * g2) = log g1 + log g2 by [].

lemma nosmt pow_mul (g1 g2:group) x: g1^x * g2^x = (g1*g2)^x.
proof.
  rewrite -{1}(gpow_log g1) -{1}(gpow_log g2) !pow_pow mul_pow.
  by rewrite !(F.mulC _ x) mulfDl F.mulC -pow_pow -mul_pow !gpow_log.
qed.

lemma nosmt pow_opp (x:group) (p:F.t): x^(-p) = inv (x^p).
proof.
  rewrite inv_def. 
  cut -> : -p = (-F.one) * p by ringeq.
  cut -> : -log (x ^ p) = (-F.one) * log(x^p) by ringeq.
  by rewrite !(F.mulC (-F.one)) -!pow_pow gpow_log.
qed.

lemma nosmt mulC (x y: group): x * y = y * x.
proof. 
  by rewrite -(gpow_log x) -(gpow_log y) mul_pow;smt. 
qed.

lemma nosmt mulA (x y z: group): x * (y * z) = x * y * z.
proof. 
  by rewrite -(gpow_log x) -(gpow_log y) -(gpow_log z) !mul_pow;smt. 
qed.

lemma nosmt mul1 x: g1 * x = x.
proof.
  by rewrite /g1 -(gpow_log x) mul_pow;smt.
qed.

lemma nosmt divK (a:group): a / a = g1.
proof strict.
  by rewrite -div_def sub_def addfN.
qed.

lemma nosmt log_g : log g = F.one.
proof strict.
 cut H: log g - log g = F.one + -log g by smt.
 cut H1: log g = log g + F.one + -log g; smt.
qed.

lemma nosmt g_neq0 : g1 <> g.
proof.
  rewrite /g1 -{2}(gpow_log g) log_g -pow_bij;smt.
qed.

lemma mulN (x:group): x * inv x = g1.
proof.
  rewrite inv_def -{1}(gpow_log x) mul_pow;smt. 
qed.

lemma inj_gpow_log (a:group): a = g ^ (log a) by smt.

hint rewrite Ring.inj_algebra : inj_gpow_log.
hint rewrite Ring.rw_algebra : log_g log_pow log_mul log_bij.

