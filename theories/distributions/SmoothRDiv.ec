require import AllCore Distr StdOrder RealFLub.
require import SDist RDiv.
(*---*) import RealOrder.

(* ==========================================================================

   Smooth max-divergence: probability preservation with both a
   multiplicative Rényi-∞ hop and an additive statistical-distance hop.

   The smooth variant is a one-lemma composition of [rdiv_inf_pr] with
   [sdist_upper_bound] — no new operator, no new predicate.  Lives in its
   own file so that [RDiv.ec] doesn't depend on [SDist.ec]; users who
   only need the pure Rényi-∞ theory pay no SDist import cost.

   The statement (event level):

     mu d1 E <= rdiv_inf d1' d2 * mu d2 E + eps

   whenever [dominated d1' d2] and [sdist d1 d1' <= eps].  This is what
   you use when [d1] is close but not absolutely continuous w.r.t. [d2]:
   slide from [d1] to a dominated neighbor [d1'], pay [eps] for the hop.

   ========================================================================== *)

(* -- Event-level smooth bound ---------------------------------------------- *)

lemma rdiv_inf_pr_smooth (d1 d1' d2 : 'a distr) (E : 'a -> bool) eps :
  dominated d1' d2 =>
  sdist d1 d1' <= eps =>
  mu d1 E <= rdiv_inf d1' d2 * mu d2 E + eps.
proof.
move => dom sd_le.
apply (ler_trans (mu d1' E + eps)).
- have := sdist_upper_bound d1 d1' E; smt().
by apply ler_add => //; exact (rdiv_inf_pr _ _ _ dom).
qed.

(* -- Distinguisher-level smooth bound -------------------------------------- *)

abstract theory SmoothDistinguisher.
type in_t, out_t.

clone import RDiv.Distinguisher as D with
  type in_t <- in_t,
  type out_t <- out_t
  proof*.

(* The sample game applied to two distributions is bounded in sdist by the
   sdist of the underlying distributions.  This is the adversary-level
   analogue of [sdist_dlet] on our transport lemma [Sample_dletE]. *)
lemma adv_sdist_sample (A <: Dist) (P : out_t -> bool) &m (d1 d2 : in_t distr) :
  `| Pr[Sample(A).main(d1) @ &m : P res]
     - Pr[Sample(A).main(d2) @ &m : P res] | <= sdist d1 d2.
proof.
rewrite !(Sample_dletE A).
pose F := fun x => mk (fun z => Pr[A.guess(x) @ &m : res = z]).
apply (ler_trans (sdist (dlet d1 F) (dlet d2 F))); first exact sdist_upper_bound.
exact sdist_dlet.
qed.

lemma adv_rdiv_inf_smooth (A <: Dist) (P : out_t -> bool) &m
                          (d1 d1' d2 : in_t distr) eps :
  dominated d1' d2 =>
  sdist d1 d1' <= eps =>
  Pr[Sample(A).main(d1) @ &m : P res] <=
    rdiv_inf d1' d2 * Pr[Sample(A).main(d2) @ &m : P res] + eps.
proof.
move => dom sd_le.
apply (ler_trans (Pr[Sample(A).main(d1') @ &m : P res] + eps)).
- have := adv_sdist_sample A P &m d1 d1'; smt().
by apply ler_add => //; apply (adv_rdiv_inf A) => //.
qed.

end SmoothDistinguisher.
