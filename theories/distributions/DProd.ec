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
apply/mulr_ile1; 1,2: apply/sumr_ge0=> />.
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
lemma mu_dprod (da : 'a distr) (db : 'b distr) Pa Pb:
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

(* -------------------------------------------------------------------- *)
(** TODO: reproduce the results on the equivalence of:
    - sampling in "da `*` db" and
    - sampling in "da", sampling in "db" and constructing the pair. **)
