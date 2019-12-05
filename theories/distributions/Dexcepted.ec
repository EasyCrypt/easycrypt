(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import AllCore Distr FSet Dfilter StdRing.
(*---*) import RField.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op (\) (d : 'a distr) (P : 'a -> bool) : 'a distr = dscale (dfilter d P).

lemma supp_dexcepted (x:'a) d P :
  support (d \ P) x <=> (support d x /\ !P x).
proof. by rewrite supp_dscale supp_dfilter /predI /predC. qed.

lemma dexcepted1E d P (x : 'a) :
  mu1 (d \ P) x
  = if   P x
    then 0%r
    else (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dscale1E weight_dfilter dfilter1E; case: (P x). qed.

lemma nosmt dexcepted1E_notin (d : 'a distr) P x:
  !P x => mu1 (d \ P) x = (mu1 d x / (weight d - mu d (P))).
proof. by rewrite dexcepted1E => ->. qed.

lemma nosmt dexcepted1E_in d P (x:'a):
  P x => mu1 (d \ P) x = 0%r.
proof. by rewrite dexcepted1E => ->. qed.

lemma dexceptedE d P (E : 'a -> bool) :
  mu (d \ P) E
  = mu d (predI E (predC (P))) / (weight d - mu d (P)).
proof. by rewrite dscaleE weight_dfilter dfilterE. qed.

lemma nosmt weight_dexcepted (d:'a distr) P :
  weight (d \ P) = b2r (weight d <> mu d (P)).
proof.
rewrite weight_dscale weight_dfilter /b2r subr_eq0.
by case: (weight d = mu d (P)).
qed.

lemma dexcepted_ll (d : 'a distr) P:
  is_lossless d => mu d P < 1%r =>
  is_lossless (d \ P).
proof.
move=> d_ll P_neq_d.
by rewrite /is_lossless  weight_dexcepted d_ll /#.
qed.

lemma dexcepted_uni (d : 'a distr) P:
  is_uniform d => is_uniform (d \ P).
proof.
move=> uni x y; rewrite !supp_dexcepted !dexcepted1E. 
by move=> [? ->] [? ->] /=; congr; apply uni.
qed.

abstract theory Sampling.

type t.

op dt: t distr.

axiom dt_ll: is_lossless dt.

module S = {
  proc direct(X : t -> bool) = {
    var r;

    r <$ dt \ X;
    return r;
  }

  proc indirect(X : t -> bool) = {
    var r;

    r <$ dt;
    if (X r) {
      r <$ dt \ X;
    }
    return r;
  }
}.

equiv direct_indirect_eq: S.direct ~ S.indirect: ={X} ==> ={res}.
proof.
bypr (res{1}) (res{2})=> /> &1 &2 a <-.
have ->: Pr[S.direct(X{1}) @ &1: res = a] = mu1 (dt \ X{1}) a.
+ by byphoare (: X = X{1} ==> _)=> //=; proc; rnd; skip.
byphoare (: X = X{1} ==> _)=> //=.
case: (a \notin dt \/ X{1} a)=> [[a_notin_dt|a_in_X]|/negb_or /= [] a_in_dt a_notin_X].
+ hoare.
  + by move: a_notin_dt; rewrite supportP dexcepted1E=> /= ->.
  proc; seq  1: (r \in dt); first by auto.
  if; auto=> [&m' _ r|/#].
  by rewrite supp_dexcepted /#.
+ conseq (: _: 0%r).
  + by move=> _ _; rewrite eq_sym -supportPn supp_dexcepted a_in_X.
  proc; seq  1: (X r) _ 0%r _ 0%r (X = X{1})=> //=.
  + by auto.
  + by rcondt 1=> //=; rnd; skip=> />; rewrite dexcepted1E a_in_X.
  by rcondf 1=> //=; hoare; skip=> /> &hr; apply/contra=> ->.
proc. alias 2 r0 = r.
phoare split (mu1 dt a) (mu dt X * mu1 (dt \ X) a): (r0 = a)=> />.
+ rewrite dexcepted1E a_notin_X /=.
  rewrite -{1}(mulr1 (mu1 dt a)) -(@divrr (weight dt - mu dt X{1})).
  + rewrite -mu_not; apply/StdOrder.RealOrder.ltr0_neq0.
    by rewrite witness_support; exists a; rewrite /predC a_notin_X a_in_dt.
  by rewrite dt_ll /#.
+ seq  2: (a = r0) (mu1 dt a) 1%r _ 0%r (r0 = r /\ X = X{1})=> //=.
  + by auto.
  + by wp; rnd (pred1 a); auto=> @/pred1.
  + by rcondf 1.
  by hoare; conseq (: _ ==> true)=> // /#.
seq  2: (!X r) _ 0%r (mu dt X) (mu1 (dt \ X) a) (r0 = r /\ X = X{1})=> //=.
+ by auto.
+ by hoare; rcondf 1=> //; skip=> /#.
+ by wp; rnd.
by rcondt 1=> //; rnd (pred1 a); skip=> /#.
qed.

end Sampling.
