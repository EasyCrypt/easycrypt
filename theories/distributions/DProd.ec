(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)

require import Pred Real RealExtra StdOrder NewDistr StdOrder.
(*---*) import RealOrder RealSeries StdBigop.Bigreal BRA.

pragma +implicits.
pragma -oldip.

(* -------------------------------------------------------------------- *)
op mprod ['a,'b] (ma : 'a -> real) (mb : 'b -> real) (ab : 'a * 'b) =
  (ma ab.`1) * (mb ab.`2).

(** This goes somewhere else and gets some lemmas attached to it **)
import List.
op unzip (s : ('a * 'b) list): 'a list * 'b list =
  foldl (fun (asbs : 'a list * 'b list) (ab : 'a * 'b)=>
           (ab.`1 :: asbs.`1,ab.`2 :: asbs.`2)) ([],[]) s.

lemma isdistr_mprod ['a,'b] (ma : 'a -> real) (mb : 'b -> real):
  isdistr ma => isdistr mb =>
  isdistr (mprod ma mb).
proof.
move=> isdistr_ml isdistr_mr; split=> [[a b]|s].
+ rewrite /mprod /=; apply/mulr_ge0.
  * by have [] -> := isdistr_ml.
  * by have [] -> := isdistr_mr.
move=> uniq_s; pose sab := (unzip s); move: sab=> [] sa sb.
have -> : big predT (mprod ma mb) s
          = (big predT ma (undup sa)) * (big predT mb (undup sb)).
+ admit. (* lots of things going on here *)
apply/mulr_ile1; 1,2: apply/sumr_ge0=> @/predT />.
+ by case: isdistr_ml.
+ by case: isdistr_mr.
+ by move: isdistr_ml=> [] _ -> //=; exact/undup_uniq.
by move: isdistr_mr=> [] _ -> //=; exact/undup_uniq.
qed.

(* -------------------------------------------------------------------- *)
(** NOTE: I suggest the use of `*` rather than simply * so we can
    unify this with the cartesian product of finite sets (where the
    quoted notation would fit better with the current notations for
    set union, intersection and difference). It would then be
    interesting to show, in the finite case, that the product of
    uniform distributions is the uniform distribution on the
    product. (Weighted distributions could be seen as drat on the
    product of the support lists.) **)
op (`*`) (da : 'a distr) (db : 'b distr) =
  mk (mprod (mu_x da) (mu_x db))
axiomatized by dprodE.

(* -------------------------------------------------------------------- *)
lemma mux_dprod (da : 'a distr) (db : 'b distr) a b:
  mu_x (da `*` db) (a,b) = mu_x da a * mu_x db b.
proof.
rewrite dprodE /mprod muK //.
by apply/(@isdistr_mprod (mu_x da) (mu_x db)); (split; [exact/ge0_mu_x|exact/le1_mu_x]).
qed.

(* -------------------------------------------------------------------- *)
lemma mu_dprod Pa Pb (da : 'a distr) (db : 'b distr):
  mu (da `*` db) (fun (ab : 'a * 'b) => Pa ab.`1 /\ Pb ab.`2)
  = mu da Pa * mu db Pb.
proof.
rewrite muE /= (@eq_sum _ (fun (ab : 'a * 'b) =>
                             (if Pa ab.`1 then mu_x da ab.`1 else 0%r)
                             * (if Pb ab.`2 then mu_x db ab.`2 else 0%r))).
+ move=> [a b] /=; rewrite mux_dprod.
  by case: (Pa a); case: (Pb b).
admit. (* lots of things going on here, same as above but with sum *)
qed.

(* -------------------------------------------------------------------- *)
lemma support_dprod (da : 'a distr) (db : 'b distr) a b:
  support (da `*` db) (a,b) <=> support da a /\ support db b.
proof. by rewrite /support /in_supp mux_dprod; smt w=mu_bounded. qed.

(* -------------------------------------------------------------------- *)
lemma weight_dprod (da : 'a distr) (db : 'b distr):
  mu (da `*` db) predT = mu da predT * mu db predT.
proof.
rewrite (@mu_eq _ _ (fun (ab : 'a * 'b)=> predT ab.`1 /\ predT ab.`2)) //.
by rewrite mu_dprod.
qed.

lemma dprod_ll (da : 'a distr) (db : 'b distr):
  is_lossless (da `*` db) <=> is_lossless da /\ is_lossless db.
proof. rewrite /is_lossless weight_dprod [smt w=mu_bounded]. qed.

(* -------------------------------------------------------------------- *)
abstract theory ProdSampling.
  type t1, t2.
  op d1 : t1 distr.
  op d2 : t2 distr.

  module S = {
    proc sample () : t1 * t2 = {
      var r;

      r <$ d1 `*` d2;
      return r;
    }

    proc sample2 () : t1 * t2 = {
      var r1, r2;

      r1 = $ d1;
      r2 = $ d2;
      return (r1,r2);
    }
  }.

  equiv sample_sample2 : S.sample ~ S.sample2 : true ==> ={res}.
  proof.
  bypr (res{1}) (res{2}) => // &m1 &m2 a.
  have ->: Pr[S.sample() @ &m1 : a = res] = mu (d1 `*` d2) (pred1 a).
  + by byphoare=> //=; proc; rnd (pred1 a); skip=> /> v; rewrite pred1E.
  elim: a=> a1 a2; have -> := mux_dprod d1 d2 a1 a2.
  byphoare=> //=.
  proc; seq  1: (a1 = r1) (mu d1 (pred1 a1)) (mu d2 (pred1 a2)) _ 0%r true=> //=.
  + by rnd (pred1 a1); skip=> /> v; rewrite pred1E.
  + by rnd (pred1 a2); skip=> /> v; rewrite pred1E.
  by hoare; auto=> /> ? ->.
  qed.
end ProdSampling.
