(* Minimal smoke test for RDiv.ec / SmoothRDiv.ec: sanity-check that the
   public API is reachable and the key lemmas apply. *)
require import AllCore Distr DList SDist RDiv SmoothRDiv.

(* [dominated d d] holds for any [d]. *)
lemma dd_dominated ['a] (d : 'a distr) : dominated d d.
proof. exact dominated_refl. qed.

(* Self-divergence is 1 on any lossless distribution. *)
lemma dd_rdiv_inf_1 ['a] (d : 'a distr) :
  is_lossless d => rdiv_inf d d = 1%r.
proof. by move=> ll; apply rdiv_inf_dd; rewrite ll. qed.

(* Probability preservation in the simplest form. *)
lemma pr_bound ['a] (d1 d2 : 'a distr) (E : 'a -> bool) :
  dominated d1 d2 => mu d1 E <= rdiv_inf d1 d2 * mu d2 E.
proof. exact rdiv_inf_pr. qed.

(* Composition: dlist scaling is power-law. *)
lemma dlist_bound ['a] (d1 d2 : 'a distr) n :
  0 <= n => dominated d1 d2 =>
  rdiv_inf (dlist d1 n) (dlist d2 n) <= RField.exp (rdiv_inf d1 d2) n.
proof. exact rdiv_inf_dlist. qed.

(* Smooth event-level: combined sdist hop + Rényi bound. *)
lemma pr_smooth_bound ['a] (d1 d1' d2 : 'a distr) E eps :
  dominated d1' d2 => sdist d1 d1' <= eps =>
  mu d1 E <= rdiv_inf d1' d2 * mu d2 E + eps.
proof. exact rdiv_inf_pr_smooth. qed.

(* Distinguisher-level: clone the [Distinguisher] theory at concrete types. *)
clone RDiv.Distinguisher as DI with
  type in_t <- int,
  type out_t <- bool
  proof*.

lemma adv_bound (A <: DI.Dist) P &m (d1 d2 : int distr) :
  dominated d1 d2 =>
  Pr[DI.Sample(A).main(d1) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[DI.Sample(A).main(d2) @ &m : P res].
proof. exact (DI.adv_rdiv_inf A). qed.
