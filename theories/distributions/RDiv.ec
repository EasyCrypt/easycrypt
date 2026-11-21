require import AllCore List Distr DProd DList Dexcepted StdBigop StdOrder RealFLub.
require import FinType.
require (*--*) SDist.
(*---*) import Bigreal RealSeries RealOrder RField BRA.

(* ==========================================================================

   Rényi divergence — max-divergence (α = ∞).

   For subdistributions [d1], [d2], the max-divergence is the supremum of
   the pointwise Radon–Nikodym derivative:

     rdiv_inf d1 d2 = sup_x (mu1 d1 x / mu1 d2 x).

   Its flagship property is *probability preservation*: for any event [E],

     mu d1 E <= M * mu d2 E.

   CAVEAT — [rdiv_inf] alone is not the max-divergence.  EasyCrypt's
   division is total with [x / 0%r = 0%r], so when [d1] is not absolutely
   continuous w.r.t. [d2] the supremum does NOT escape to +∞: points where
   [mu1 d2 x = 0] contribute ratio 0, and [rdiv_inf d1 d2] evaluates to a
   well-defined but cryptographically meaningless finite value — e.g.
   [rdiv_inf (duniform [a; b]) (dunit a) = 1%r/2%r] although the true
   max-divergence is infinite and probability preservation fails.  A bare
   inequality [rdiv_inf d1 d2 <= M] therefore carries no guarantee by
   itself.  The meaningful hypothesis is the predicate [dominated M d1 d2]
   ([M >= 0] plus the pointwise bound [mu1 d1 x <= M * mu1 d2 x]): every
   lemma below is guarded by it, and downstream developments must state
   their assumptions via [dominated] (or pair any [rdiv_inf] bound with a
   [dominated] witness), never via bare [rdiv_inf] inequalities.

   Contents:
     Definitions    — [dominated], [rdiv_inf].
     Section 1      — Dominance and basic bounds.
     Section 2      — Probability preservation ([dominated_pr], [rdiv_inf_pr]).
     Section 3      — Structural lemmas: dmap, dlet, dprod, dlist,
                      dexcepted, drestrict, dcond, djoinmap, djoin,
                      dfst, dsnd, dopt, dlet_dep (dependent kernels), dfold.
     [RDivFun]      — abstract theory: [dominated_dfun] (+[_cst]),
                      [rdiv_inf_dfun] (clone with [theory FT <- YourFinType]).
     [Distinguisher] — abstract theory: [Sample] game, [Sample_dletE]
                      (Pr-to-distr transport), [adv_rdiv_inf],
                      [adv_rdiv_inf_le], fused variants (dmap, dlet,
                      dexcepted, dcond).
     [DistinguisherList] — abstract theory: [adv_rdiv_inf_dlist].

   Companion file:
     [RDivOracle.ec] — oracle-access bound via presampling
                       ([rdiv_bound_sampler]).

   ========================================================================== *)

(* -- Dominance predicate --------------------------------------------------- *)

(* [dominated M d1 d2]: d1 is M-dominated by d2 — the pointwise ratio is
   bounded by M.  Equivalent to absolute continuity plus a bounded
   Radon–Nikodym derivative with explicit bound. *)
pred dominated (M : real) (d1 d2 : 'a distr) =
  0%r <= M /\ forall x, mu1 d1 x <= M * mu1 d2 x.

(* -- Max-divergence -------------------------------------------------------- *)

op rdiv_inf (d1 d2 : 'a distr) =
  flub (fun x => mu1 d1 x / mu1 d2 x).

(* ==========================================================================
   Section 1 — dominance and basic bounds.
   ========================================================================== *)

lemma dominated_refl (d : 'a distr) : dominated 1%r d d.
proof. by split => // x; rewrite mul1r. qed.

lemma dominated_ac (M : real) (d1 d2 : 'a distr) x :
  dominated M d1 d2 => mu1 d2 x = 0%r => mu1 d1 x = 0%r.
proof.
case => [_ le_mu1] mu2x_eq0.
have := le_mu1 x; rewrite mu2x_eq0 mulr0.
smt(ge0_mu1).
qed.

lemma has_fub_ratio (M : real) (d1 d2 : 'a distr) :
  dominated M d1 d2 => has_fub (fun x => mu1 d1 x / mu1 d2 x).
proof.
case => [ge0_M le_mu1]; exists M => x /=.
case (mu1 d2 x = 0%r) => [-> | ne0].
- by rewrite invr0 mulr0.
- have pos : 0%r < mu1 d2 x by smt(ge0_mu1).
  by rewrite ler_pdivr_mulr //; apply le_mu1.
qed.

(* The defining sup form, exposed as a rewrite rule. *)
lemma rdiv_infE (d1 d2 : 'a distr) :
  rdiv_inf d1 d2 = flub (fun x => mu1 d1 x / mu1 d2 x).
proof. by []. qed.

lemma rdiv_inf_upper_bound (M : real) (d1 d2 : 'a distr) x :
  dominated M d1 d2 => mu1 d1 x <= rdiv_inf d1 d2 * mu1 d2 x.
proof.
move => dom.
have hf := has_fub_ratio M _ _ dom.
have ratio_le : mu1 d1 x / mu1 d2 x <= rdiv_inf d1 d2.
  by apply (flub_upper_bound<:'a> (fun x => mu1 d1 x / mu1 d2 x) x).
case (mu1 d2 x = 0%r) => [eq0 | ne0].
- by rewrite eq0 mulr0 (dominated_ac M _ _ _ dom eq0).
- have pos : 0%r < mu1 d2 x by smt(ge0_mu1).
  by rewrite -(ler_pdivr_mulr _ _ _ pos).
qed.

lemma rdiv_inf_le_ub (d1 d2 : 'a distr) (r : real) :
  0%r <= r =>
  (forall x, mu1 d1 x <= r * mu1 d2 x) =>
  rdiv_inf d1 d2 <= r.
proof.
move => ge0_r le_r; apply flub_le_ub => x /=.
case (mu1 d2 x = 0%r) => [eq0 | ne0].
- have mu1_eq0 : mu1 d1 x = 0%r.
  + by have := le_r x; rewrite eq0 mulr0; smt(ge0_mu1).
  by rewrite mu1_eq0 eq0 invr0 mulr0.
- have pos : 0%r < mu1 d2 x by smt(ge0_mu1).
  by rewrite ler_pdivr_mulr //; apply le_r.
qed.

(* [rdiv_inf_le]: any explicit M that dominates yields an upper bound. *)
lemma rdiv_inf_le (M : real) (d1 d2 : 'a distr) :
  dominated M d1 d2 => rdiv_inf d1 d2 <= M.
proof. by case => [ge0_M le_mu1]; apply rdiv_inf_le_ub. qed.

lemma rdiv_inf_ge0 (M : real) (d1 d2 : 'a distr) :
  dominated M d1 d2 => 0%r <= rdiv_inf d1 d2.
proof.
move => dom.
have hf := has_fub_ratio M _ _ dom.
(* Every value of the ratio is >= 0; pick [witness]. *)
apply (ler_trans (mu1 d1 witness / mu1 d2 witness)); last first.
- by apply (flub_upper_bound<:'a> (fun x => mu1 d1 x / mu1 d2 x) witness).
smt(ge0_mu1 invr_ge0 mulr_ge0).
qed.

(* The tight dominance witness: [rdiv_inf d1 d2] is itself a valid M. *)
lemma rdiv_inf_dominated (M : real) (d1 d2 : 'a distr) :
  dominated M d1 d2 => dominated (rdiv_inf d1 d2) d1 d2.
proof.
move => dom; split.
- exact (rdiv_inf_ge0 M _ _ dom).
- move => x; exact (rdiv_inf_upper_bound M _ _ x dom).
qed.

(* Reflexive case.  When [weight d = 0] the distribution is [dnull] and the
   ratio is 0/0 = 0 everywhere, giving rdiv_inf d d = 0, not 1. *)
lemma rdiv_inf_dd (d : 'a distr) :
  0%r < weight d => rdiv_inf d d = 1%r.
proof.
move => pos_w; apply ler_anti; split => [|_].
- by apply rdiv_inf_le_ub => // x; rewrite mul1r.
(* There exists x0 with mu1 d x0 > 0; at that x0 the ratio is 1. *)
have [x0 pos] : exists x, 0%r < mu1 d x.
- have: 0%r < mu d predT by apply pos_w.
  move=> /witness_support [x0 [_ in_d]].
  have ne0 : mu1 d x0 <> 0%r by apply/supportP.
  exists x0; rewrite lt0r; split; [exact ne0 | apply ge0_mu1].
apply (ler_trans (mu1 d x0 / mu1 d x0)); first by smt(divff).
apply (flub_upper_bound<:'a> (fun x => mu1 d x / mu1 d x) x0).
by apply (has_fub_ratio 1%r); exact dominated_refl.
qed.

(* dnull case. *)
lemma rdiv_inf_dnull (d : 'a distr) :
  rdiv_inf dnull<:'a> d = 0%r.
proof.
apply ler_anti; split => [|_].
- by apply rdiv_inf_le_ub => // x; rewrite mul0r dnull1E.
by apply (rdiv_inf_ge0 0%r); split => // x; rewrite mul0r dnull1E.
qed.

(* ==========================================================================
   Section 2 — probability preservation.
   ========================================================================== *)

(* Direct bound with the user-supplied M. *)
lemma dominated_pr (M : real) (d1 d2 : 'a distr) E :
  dominated M d1 d2 => mu d1 E <= M * mu d2 E.
proof.
case => [ge0_M le_mu1].
rewrite muE (muE d2) -sumZ.
apply ler_sum => [x /= | |].
- case (E x) => _; last by rewrite mulr0.
  exact (le_mu1 x).
- exact/summable_cond/summable_mu1.
- apply (summable_le_pos _ (fun x => M * mu1 d2 x)) => /=.
  + exact/summableZ/summable_mu1.
  move => x; case (E x) => _; smt(ge0_mu1 mulr_ge0).
qed.

(* Tight bound via [rdiv_inf]. *)
lemma rdiv_inf_pr (M : real) (d1 d2 : 'a distr) E :
  dominated M d1 d2 => mu d1 E <= rdiv_inf d1 d2 * mu d2 E.
proof.
move => dom; exact (dominated_pr _ _ _ _ (rdiv_inf_dominated M _ _ dom)).
qed.

(* ==========================================================================
   Section 3 — data-processing and composition.

   All bounds here are consequences of the pointwise upper bound:
     mu1 d1 x <= M * mu1 d2 x
   applied to the appropriate event or sum.

   The "dominated" lemma propagates the explicit bound M through the
   construction; the "rdiv_inf" lemma gives the tighter bound via
   the supremum of the pointwise ratio.

   PROOF DISCIPLINE: every [rdiv_inf_*] bound below is its [dominated_*]
   counterpart applied at the tight witness [rdiv_inf d1 d2] (via
   [rdiv_inf_dominated]), then closed by [rdiv_inf_le].  No structural
   argument is proved twice: to audit a pair, read the [dominated_*]
   proof; the [rdiv_inf_*] one is an instance of this single principle.
   ========================================================================== *)

(* -- dmap ------------------------------------------------------------------ *)

lemma dominated_dmap (M : real) (d1 d2 : 'a distr) (F : 'a -> 'b) :
  dominated M d1 d2 => dominated M (dmap d1 F) (dmap d2 F).
proof.
move => dom; split; first by case: dom.
move => b; rewrite !dmap1E.
exact (dominated_pr M _ _ _ dom).
qed.

lemma rdiv_inf_dmap (M : real) (d1 d2 : 'a distr) (F : 'a -> 'b) :
  dominated M d1 d2 => rdiv_inf (dmap d1 F) (dmap d2 F) <= rdiv_inf d1 d2.
proof.
by move => dom; apply/rdiv_inf_le/dominated_dmap/(rdiv_inf_dominated M).
qed.

(* -- dlet ------------------------------------------------------------------ *)

(* Pointwise upper bound for [dlet].  Shared by [dominated_dlet] and
   [rdiv_inf_dlet]. *)
lemma dlet_pointwise (M : real) (d1 d2 : 'a distr) (F : 'a -> 'b distr) y :
  dominated M d1 d2 =>
  mu1 (dlet d1 F) y <= M * mu1 (dlet d2 F) y.
proof.
case => [ge0_M le_mu1]; rewrite !dlet1E -sumZ.
apply ler_sum => [x /= | |].
- rewrite mulrA; apply ler_wpmul2r; first exact ge0_mu1.
  exact (le_mu1 x).
- by apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
- apply summableZ; apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
qed.

lemma dominated_dlet (M : real) (d1 d2 : 'a distr) (F : 'a -> 'b distr) :
  dominated M d1 d2 => dominated M (dlet d1 F) (dlet d2 F).
proof.
move => dom; split; first by case: dom.
by move => y; apply (dlet_pointwise M).
qed.

lemma rdiv_inf_dlet (M : real) (d1 d2 : 'a distr) (F : 'a -> 'b distr) :
  dominated M d1 d2 => rdiv_inf (dlet d1 F) (dlet d2 F) <= rdiv_inf d1 d2.
proof.
by move => dom; apply/rdiv_inf_le/dominated_dlet/(rdiv_inf_dominated M).
qed.

(* -- dprod ----------------------------------------------------------------- *)

lemma dprod_pointwise (Ml Mr : real) (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) p :
  dominated Ml dl1 dl2 => dominated Mr dr1 dr2 =>
  mu1 (dl1 `*` dr1) p <= (Ml * Mr) * mu1 (dl2 `*` dr2) p.
proof.
case => [ge0_Ml le_l]; case => [ge0_Mr le_r].
case: p => a b; rewrite !dprod1E.
have -> :
  Ml * Mr * (mu1 dl2 a * mu1 dr2 b)
  = (Ml * mu1 dl2 a) * (Mr * mu1 dr2 b) by ring.
by apply ler_pmul; smt(ge0_mu1).
qed.

lemma dominated_dprod (Ml Mr : real) (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  dominated Ml dl1 dl2 => dominated Mr dr1 dr2 =>
  dominated (Ml * Mr) (dl1 `*` dr1) (dl2 `*` dr2).
proof.
move => doml domr; split.
- by case: doml => [??]; case: domr => [??]; apply mulr_ge0.
by move => p; apply (dprod_pointwise Ml Mr).
qed.

lemma rdiv_inf_dprod (Ml Mr : real) (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  dominated Ml dl1 dl2 => dominated Mr dr1 dr2 =>
  rdiv_inf (dl1 `*` dr1) (dl2 `*` dr2) <= rdiv_inf dl1 dl2 * rdiv_inf dr1 dr2.
proof.
move => doml domr; apply rdiv_inf_le.
by apply dominated_dprod;
  [exact (rdiv_inf_dominated Ml) | exact (rdiv_inf_dominated Mr)].
qed.

(* -- dlist ----------------------------------------------------------------- *)

lemma dominated_dlist (M : real) (d1 d2 : 'a distr) n :
  0 <= n => dominated M d1 d2 =>
  dominated (RField.exp M n) (dlist d1 n) (dlist d2 n).
proof.
move => ge0_n dom; elim: n ge0_n => [|n ge0_n IHn].
- by rewrite !dlist0 // RField.expr0; exact dominated_refl.
rewrite !dlistS // RField.exprS //.
apply dominated_dmap.
exact (dominated_dprod M (RField.exp M n) _ _ _ _ dom IHn).
qed.

lemma rdiv_inf_dlist (M : real) (d1 d2 : 'a distr) n :
  0 <= n => dominated M d1 d2 =>
  rdiv_inf (dlist d1 n) (dlist d2 n) <= RField.exp (rdiv_inf d1 d2) n.
proof.
move => ge0_n dom; apply rdiv_inf_le.
by apply dominated_dlist => //; exact (rdiv_inf_dominated M).
qed.

(* -- dexcepted / drestrict / dcond ----------------------------------------

   Code-level rejection and conditioning.  These come up every time a
   cryptographic scheme uses rejection sampling or samples conditional on
   an event, and the Rényi cost is simply [1 / (1 - rejection prob)]. *)

(* [d \ P]: reject [P]-satisfying elements, rescale to weight 1.
   Ratio [mu1 (d \ P) x / mu1 d x] is [1/(weight d - mu d P)] for [!P x],
   and 0 otherwise.  Cite this whenever you have a rejection step. *)
lemma dominated_dexcepted (d : 'a distr) (P : 'a -> bool) :
  mu d P < weight d =>
  dominated (1%r / (weight d - mu d P)) (d \ P) d.
proof.
move => lt_P.
pose M := 1%r / (weight d - mu d P).
have pos_wP : 0%r < weight d - mu d P by rewrite subr_gt0.
have ge0_M : 0%r <= M by rewrite /M; smt(invr_gt0).
split => // x; rewrite dexcepted1E.
case (P x) => _.
- by rewrite /M; smt(ge0_mu1 mulr_ge0 invr_gt0).
by rewrite /M; smt(ge0_mu1).
qed.

lemma rdiv_inf_dexcepted (d : 'a distr) (P : 'a -> bool) :
  mu d P < weight d =>
  rdiv_inf (d \ P) d <= 1%r / (weight d - mu d P).
proof.
by move => lt_P; exact/rdiv_inf_le/dominated_dexcepted.
qed.

(* Lossless specialization — the crypto-facing form.  For a lossless [d]
   with rejection probability [mu d P], the Rényi-∞ cost is [1/Pr[!P]]. *)
lemma rdiv_inf_dexcepted_ll (d : 'a distr) (P : 'a -> bool) :
  is_lossless d => mu d P < 1%r =>
  rdiv_inf (d \ P) d <= 1%r / (1%r - mu d P).
proof.
move => ll_d lt_P; have := rdiv_inf_dexcepted d P _; smt().
qed.

(* [drestrict d P]: zero out [!P], no rescaling — stays sub-distribution.
   Trivially dominated by [d]. *)
lemma dominated_drestrict (d : 'a distr) (P : 'a -> bool) :
  dominated 1%r (drestrict d P) d.
proof.
split => // x; rewrite drestrict1E mul1r.
by case (P x) => _; smt(ge0_mu1).
qed.

lemma rdiv_inf_drestrict (d : 'a distr) (P : 'a -> bool) :
  rdiv_inf (drestrict d P) d <= 1%r.
proof.
exact/rdiv_inf_le/dominated_drestrict.
qed.

(* [dcond d P = dscale (drestrict d P)]: condition on [P] (normalize).
   Equivalent to [d \ (predC P)]. *)
lemma dominated_dcond (d : 'a distr) (P : 'a -> bool) :
  0%r < mu d P =>
  dominated (1%r / mu d P) (dcond d P) d.
proof.
move => pos_P.
pose M := 1%r / mu d P.
have ge0_M : 0%r <= M by rewrite /M; smt(invr_gt0).
split => // x; rewrite dcond1E.
case (P x) => _.
- by rewrite /M; smt(ge0_mu1 mulr_ge0 invr_gt0).
by rewrite /M; smt(ge0_mu1 mulr_ge0).
qed.

lemma rdiv_inf_dcond (d : 'a distr) (P : 'a -> bool) :
  0%r < mu d P =>
  rdiv_inf (dcond d P) d <= 1%r / mu d P.
proof.
by move => pos_P; exact/rdiv_inf_le/dominated_dcond.
qed.

(* -- djoinmap -------------------------------------------------------------

   [djoinmap F xs = djoin (map F xs)]: the heterogeneous product of a list
   of distributions indexed by [xs].  Generalizes [dlist] (which is the
   homogeneous case).  The Rényi cost multiplies across indices; the
   per-index bounds [Mf x] need not be uniform ([_cst] gives the uniform
   corollary with cost [M ^ size xs]). *)
lemma dominated_djoinmap ['a 'b] (Mf : 'a -> real) (F1 F2 : 'a -> 'b distr) (xs : 'a list) :
  (forall x, x \in xs => dominated (Mf x) (F1 x) (F2 x)) =>
  dominated (BRM.big predT Mf xs) (djoinmap F1 xs) (djoinmap F2 xs).
proof.
elim: xs => [_|x xs IHxs dom_cons] /=.
- by rewrite BRM.big_nil; exact dominated_refl.
have dom_head := dom_cons x _; first by rewrite mem_head.
have dom_tail : dominated (BRM.big predT Mf xs) (djoinmap F1 xs) (djoinmap F2 xs).
- by apply IHxs => y y_in; apply dom_cons; rewrite in_cons y_in.
rewrite !djoin_cons BRM.big_cons /predT /=.
apply dominated_dmap.
exact (dominated_dprod (Mf x) (BRM.big predT Mf xs) _ _ _ _ dom_head dom_tail).
qed.

lemma dominated_djoinmap_cst ['a 'b] (M : real) (F1 F2 : 'a -> 'b distr) (xs : 'a list) :
  (forall x, x \in xs => dominated M (F1 x) (F2 x)) =>
  dominated (RField.exp M (size xs)) (djoinmap F1 xs) (djoinmap F2 xs).
proof.
move => dom.
have := dominated_djoinmap (fun _ => M) F1 F2 xs dom.
by rewrite mulr_const.
qed.

lemma rdiv_inf_djoinmap ['a 'b] (Mf : 'a -> real) (F1 F2 : 'a -> 'b distr) (xs : 'a list) :
  (forall x, x \in xs => dominated (Mf x) (F1 x) (F2 x)) =>
  rdiv_inf (djoinmap F1 xs) (djoinmap F2 xs) <=
    BRM.big predT (fun x => rdiv_inf (F1 x) (F2 x)) xs.
proof.
move => dom; apply rdiv_inf_le.
apply (dominated_djoinmap (fun x => rdiv_inf (F1 x) (F2 x))) => x x_in /=.
exact (rdiv_inf_dominated (Mf x) _ _ (dom x x_in)).
qed.

(* -- djoin ----------------------------------------------------------------

   [djoin (ds : 'a distr list) : 'a list distr] is the heterogeneous
   product of a list of distributions.  One-line corollary of djoinmap
   via the identity realization. *)

lemma djoinmap_nth ['a] (ds : 'a distr list) :
  djoinmap (fun i => nth witness ds i) (range 0 (size ds)) = djoin ds.
proof. by congr; apply map_nth_range. qed.

lemma dominated_djoin ['a] (M : real) (ds1 ds2 : 'a distr list) :
  size ds1 = size ds2 =>
  (forall i, 0 <= i < size ds1 =>
     dominated M (nth witness ds1 i) (nth witness ds2 i)) =>
  dominated (RField.exp M (size ds1)) (djoin ds1) (djoin ds2).
proof.
move => eq_sz dom_pt.
rewrite -(djoinmap_nth ds1) -(djoinmap_nth ds2) -eq_sz.
have -> : RField.exp M (size ds1)
        = RField.exp M (size (range 0 (size ds1))).
- by congr; rewrite size_range; smt(size_ge0).
by apply dominated_djoinmap_cst => i /mem_range rg_i; exact (dom_pt i rg_i).
qed.

lemma rdiv_inf_djoin ['a] (M : real) (ds1 ds2 : 'a distr list) :
  size ds1 = size ds2 =>
  (forall i, 0 <= i < size ds1 =>
     dominated M (nth witness ds1 i) (nth witness ds2 i)) =>
  rdiv_inf (djoin ds1) (djoin ds2) <=
    BRM.big predT (fun i => rdiv_inf (nth witness ds1 i) (nth witness ds2 i))
                   (range 0 (size ds1)).
proof.
move => eq_sz dom_pt.
rewrite -(djoinmap_nth ds1) -(djoinmap_nth ds2) -eq_sz.
by apply (rdiv_inf_djoinmap (fun _ => M)) => i /mem_range rg_i; exact (dom_pt i rg_i).
qed.

(* -- dfst / dsnd ---------------------------------------------------------

   Marginals of a pair distribution.  Trivially follows from dmap. *)

lemma dominated_dfst ['a 'b] (M : real) (d1 d2 : ('a * 'b) distr) :
  dominated M d1 d2 => dominated M (dfst d1) (dfst d2).
proof. exact (dominated_dmap M _ _ fst). qed.

lemma rdiv_inf_dfst ['a 'b] (M : real) (d1 d2 : ('a * 'b) distr) :
  dominated M d1 d2 => rdiv_inf (dfst d1) (dfst d2) <= rdiv_inf d1 d2.
proof. exact (rdiv_inf_dmap M _ _ fst). qed.

lemma dominated_dsnd ['a 'b] (M : real) (d1 d2 : ('a * 'b) distr) :
  dominated M d1 d2 => dominated M (dsnd d1) (dsnd d2).
proof. exact (dominated_dmap M _ _ snd). qed.

lemma rdiv_inf_dsnd ['a 'b] (M : real) (d1 d2 : ('a * 'b) distr) :
  dominated M d1 d2 => rdiv_inf (dsnd d1) (dsnd d2) <= rdiv_inf d1 d2.
proof. exact (rdiv_inf_dmap M _ _ snd). qed.

(* -- dopt ----------------------------------------------------------------

   [dopt d : 'a option distr] adds a [None] branch with the remaining
   mass [1 - weight d].  If [d2]'s weight is at most [d1]'s (so [dopt d1]
   puts no more mass on [None] than [dopt d2] does), dominance is
   preserved up to [maxr 1%r M] — the [None] branch may need factor 1
   even when [M < 1]. *)

lemma dominated_dopt (M : real) (d1 d2 : 'a distr) :
  weight d2 <= weight d1 =>
  dominated M d1 d2 =>
  dominated (maxr 1%r M) (dopt d1) (dopt d2).
proof.
move => le_w dom.
case: dom => [ge0_M le_mu1]; split; first smt().
case => [|y]; rewrite !dopt1E /=.
- smt(mu_bounded).
apply (ler_trans (M * mu1 d2 y)); first exact (le_mu1 y).
apply ler_wpmul2r; smt(ge0_mu1).
qed.

lemma rdiv_inf_dopt (M : real) (d1 d2 : 'a distr) :
  weight d2 <= weight d1 =>
  dominated M d1 d2 =>
  rdiv_inf (dopt d1) (dopt d2) <= maxr 1%r (rdiv_inf d1 d2).
proof.
move => le_w dom; apply rdiv_inf_le.
by apply dominated_dopt => //; exact (rdiv_inf_dominated M).
qed.

(* -- Dependent-kernel dlet dominance --------------------------------------

   Strengthens [dominated_dlet] to allow the kernel to differ between the
   two sides, at the cost of a *uniform* pointwise bound on the kernel (a
   single constant [Mf]).  The kernel bound is only required on the
   support of [d1] — parameterized families are typically dominated only
   at well-formed parameters. *)

lemma dominated_dlet_dep ['a 'b] (Md Mf : real) (d1 d2 : 'a distr) (F1 F2 : 'a -> 'b distr) :
  0%r <= Mf =>
  dominated Md d1 d2 =>
  (forall x, x \in d1 => dominated Mf (F1 x) (F2 x)) =>
  dominated (Md * Mf) (dlet d1 F1) (dlet d2 F2).
proof.
move => ge0_Mf; case => [ge0_Md dom_d] dom_F.
split; first by apply mulr_ge0.
move => y; rewrite !dlet1E -sumZ.
apply ler_sum => [x /= | |].
- case (x \in d1) => [x_in | x_nin]; last first.
  + have -> : mu1 d1 x = 0%r by smt(supportP).
    by rewrite mul0r; smt(ge0_mu1 mulr_ge0).
  have h1 := dom_d x.
  have [_ h2] := dom_F x x_in; have h2' := h2 y.
  have : mu1 d1 x * mu1 (F1 x) y <= (Md * mu1 d2 x) * (Mf * mu1 (F2 x) y).
  + by apply ler_pmul; smt(ge0_mu1).
  by rewrite mulrACA.
- apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
- apply summableZ; apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
qed.

(* -- dfold ---------------------------------------------------------------

   [dfold f x n] iterates [f] for [n] steps starting from [x].  Analogue
   of [dlist] for state-carrying iteration.  The Rényi cost composes
   multiplicatively over the loop. *)

(* Dominance of [dfold] under step-wise domination.  The per-step bound
   [Ms i] dominates the i-th step's kernel at every accumulator value
   *reachable* by the first i steps ([y \in dfold f1 x i]) — unreachable
   states need no bound.  Conclusion: the product of step-wise bounds. *)
lemma dominated_dfold ['a] (f1 f2 : int -> 'a -> 'a distr) (x : 'a) (n : int)
      (Ms : int -> real) :
  0 <= n =>
  (forall i, 0 <= i < n =>
     0%r <= Ms i /\
     forall y, y \in dfold f1 x i =>
       forall z, mu1 (f1 i y) z <= Ms i * mu1 (f2 i y) z) =>
  dominated (BRM.big predT Ms (range 0 n)) (dfold f1 x n) (dfold f2 x n).
proof.
move => ge0_n; elim: n ge0_n => [|n ge0_n IHn] step.
- by rewrite !dfold0 range_geq // BRM.big_nil; exact dominated_refl.
rewrite !dfoldS // BRM.big_int_recr //.
have IH := IHn _; first by move => i rng_i; apply step; smt().
have [ge0_Mn step_n] := step n _; first smt().
apply (dominated_dlet_dep (BRM.big predT Ms (range 0 n)) (Ms n) _ _ _ _ ge0_Mn IH).
by move => y y_in; split => //; exact (step_n y y_in).
qed.

(* rdiv_inf bound for dfold — corollary of [dominated_dfold]. *)
lemma rdiv_inf_dfold ['a] (f1 f2 : int -> 'a -> 'a distr) (x : 'a) (n : int)
      (Ms : int -> real) :
  0 <= n =>
  (forall i, 0 <= i < n =>
     0%r <= Ms i /\
     forall y, y \in dfold f1 x i =>
       forall z, mu1 (f1 i y) z <= Ms i * mu1 (f2 i y) z) =>
  rdiv_inf (dfold f1 x n) (dfold f2 x n) <= BRM.big predT Ms (range 0 n).
proof.
move => ge0_n step.
exact (rdiv_inf_le _ _ _ (dominated_dfold f1 f2 x n Ms ge0_n step)).
qed.

(* -- dfun ----------------------------------------------------------------

   [dfun F : (t -> 'u) distr] samples a function over a finite domain
   [t] by sampling [F x] at each point independently.  Rényi multiplies
   across the domain.  [dfun] requires a [FinType] on [t], so unlike
   the structural lemmas above this is an abstract theory.  Clone with
   [theory FT <- YourFinType]; the internal [MUniFinFun] is wired
   automatically.  If [YourFinType] is itself a direct [FinType] clone,
   instantiate its [t] with [<=], not [<-]: the outer [theory FT <- ...]
   matches on [t], and [<-] clears the very symbol it matches on.  (A
   clone that only substitutes *upstream* parameters is unaffected — e.g.
   [FinProdType with type t1 <- ..., type t2 <- ...] leaves [t] intact.)
   See the [Iface] clone in [RDivOracle.ec] for a worked instance. *)

abstract theory RDivFun.
  clone FinType as FT.

  clone import MUniFinFun with
    type t      <- FT.t,
    theory FinT <- FT
    proof *.

  lemma dominated_dfun ['u] (Mf : FT.t -> real) (F1 F2 : FT.t -> 'u distr) :
    (forall x, dominated (Mf x) (F1 x) (F2 x)) =>
    dominated (BRM.big predT Mf FT.enum) (dfun F1) (dfun F2).
  proof.
  move => dom_pt; rewrite !dfun_dmap; apply dominated_dmap.
  by apply dominated_djoinmap => x _; exact (dom_pt x).
  qed.

  lemma dominated_dfun_cst ['u] (M : real) (F1 F2 : FT.t -> 'u distr) :
    (forall x, dominated M (F1 x) (F2 x)) =>
    dominated (RField.exp M (size FT.enum)) (dfun F1) (dfun F2).
  proof.
  move => dom_pt.
  have := dominated_dfun (fun _ => M) F1 F2 dom_pt.
  by rewrite mulr_const.
  qed.

  lemma rdiv_inf_dfun ['u] (M : real) (F1 F2 : FT.t -> 'u distr) :
    (forall x, dominated M (F1 x) (F2 x)) =>
    rdiv_inf (dfun F1) (dfun F2) <=
      BRM.big predT (fun x => rdiv_inf (F1 x) (F2 x)) FT.enum.
  proof.
  move => dom_pt; apply rdiv_inf_le.
  apply (dominated_dfun (fun x => rdiv_inf (F1 x) (F2 x))) => x /=.
  exact (rdiv_inf_dominated M _ _ (dom_pt x)).
  qed.

end RDivFun.

(* ==========================================================================
   Section 4 — Distinguisher layer.

   Lifts probability preservation from events to adversaries.  The main
   lemma [adv_rdiv_inf] says:

     Pr[Sample(A).main(d1) @ &m : P res]
       <= rdiv_inf d1 d2 * Pr[Sample(A).main(d2) @ &m : P res].

   Design:
   - Generic output type [out_t], not just bool — events [P : out_t -> bool]
     transport through unchanged.
   - Distributions are [main] arguments, not theory parameters, so a single
     clone serves every pair of distributions.
   - The Pr-to-distr transport machinery ([S], [sampleE], [adv_isdistr],
     [adv_mu1]) is reused from [SDist.GenDist] rather than re-proved.
   ========================================================================== *)

abstract theory Distinguisher.
type in_t, out_t.

module type Dist = {
  proc guess(x : in_t) : out_t
}.

(* Pr-to-distr transport: [S], [sampleE], [uniq_big_res], [adv_isdistr],
   [adv_mu1].  [GD.Distinguisher] is structurally identical to [Dist]. *)
clone import SDist.GenDist as GD with
  type in_t  <- in_t,
  type out_t <- out_t
  proof*.

clone import DProd.DLetSampling as DLS with
  type t <- in_t,
  type u <- out_t
  proof*.

(* The sample-then-distinguish game.  Users reshape their concrete
   adversaries into this shape to cite [adv_rdiv_inf]. *)
module Sample (A : Dist) = {
  proc main(d : in_t distr) = {
    var x, r;

    x <$ d;
    r <@ A.guess(x);
    return r;
  }
}.

(* Main transport lemma: the adversary game reduces to a [dlet].
   The continuation [F x] is the output distribution of [A.guess(x)]. *)
lemma Sample_dletE (A <: Dist) (P : out_t -> bool) &m d' :
  Pr[Sample(A).main(d') @ &m : P res] =
  mu (dlet d' (fun x => mk (fun z => Pr[A.guess(x) @ &m : res = z]))) P.
proof.
pose F := fun x => mk (fun z => Pr[A.guess(x) @ &m : res = z]).
have -> : Pr[Sample(A).main(d') @ &m : P res] =
          Pr[SampleDep.sample(d', F) @ &m : P res].
- byequiv => //; proc.
  seq 1 1 : ((glob A){1} = (glob A){m} /\ du{2} = F /\ x{1} = t{2}); first by auto.
  outline {2} 1 ~ S.sample.
  call (: d{2} = (F x){1} /\ (glob A){1} = (glob A){m} ==> ={res}).
  bypr (res{1}) (res{2}); first smt().
  move => &1 &2 a [-> eq_globA]; rewrite sampleE -(adv_mu1 A).
  byequiv (: ={x, glob A} ==> ={res}) => //; 1: by sim.
  by auto.
have -> : Pr[SampleDep.sample(d', F) @ &m : P res] =
          Pr[SampleDLet.sample(d', F) @ &m : P res].
- by byequiv => //; conseq SampleDepDLet; move: F; auto.
byphoare (: dt = d' /\ du = F ==> _) => //; proc.
by rnd; skip => /> &1 -> ->.
qed.

(* Flagship: probability preservation at the adversary level. *)
lemma adv_rdiv_inf (A <: Dist) (P : out_t -> bool) &m (M : real) (d1 d2 : in_t distr) :
  dominated M d1 d2 =>
  Pr[Sample(A).main(d1) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(d2) @ &m : P res].
proof.
move => dom.
rewrite !(Sample_dletE A).
pose F := fun x => mk (fun z => Pr[A.guess(x) @ &m : res = z]).
apply (ler_trans (rdiv_inf (dlet d1 F) (dlet d2 F) * mu (dlet d2 F) P)).
- exact (rdiv_inf_pr M _ _ P (dominated_dlet M _ _ F dom)).
apply ler_wpmul2r; first exact ge0_mu.
exact (rdiv_inf_dlet M _ _ F dom).
qed.

(* [adv_rdiv_inf] with the divergence replaced by any explicit upper
   bound — the form every composed variant below reduces to. *)
lemma adv_rdiv_inf_le (A <: Dist) (P : out_t -> bool) &m
                      (M r : real) (d1 d2 : in_t distr) :
  dominated M d1 d2 => rdiv_inf d1 d2 <= r =>
  Pr[Sample(A).main(d1) @ &m : P res] <=
    r * Pr[Sample(A).main(d2) @ &m : P res].
proof.
move => dom le_r.
apply (ler_trans (rdiv_inf d1 d2 * Pr[Sample(A).main(d2) @ &m : P res])).
- exact (adv_rdiv_inf A P &m M _ _ dom).
by apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
qed.

(* -- Pre-composed adversary bounds ----------------------------------------

   Fuse [adv_rdiv_inf] with the structural lemmas so users cite a single
   composed result instead of chaining three applications. *)

lemma adv_rdiv_inf_dmap ['a] (A <: Dist) (P : out_t -> bool) &m
                        (M : real) (G : 'a -> in_t) (d1 d2 : 'a distr) :
  dominated M d1 d2 =>
  Pr[Sample(A).main(dmap d1 G) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(dmap d2 G) @ &m : P res].
proof.
move => dom; apply (adv_rdiv_inf_le A P &m M).
- exact (dominated_dmap M).
- exact (rdiv_inf_dmap M).
qed.

lemma adv_rdiv_inf_dlet ['a] (A <: Dist) (P : out_t -> bool) &m
                        (M : real) (G : 'a -> in_t distr) (d1 d2 : 'a distr) :
  dominated M d1 d2 =>
  Pr[Sample(A).main(dlet d1 G) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(dlet d2 G) @ &m : P res].
proof.
move => dom; apply (adv_rdiv_inf_le A P &m M).
- exact (dominated_dlet M).
- exact (rdiv_inf_dlet M).
qed.

(* Rejection sampling: the sample source is [d \ Q] — the adversary sees
   a sample from [d] restricted to [!Q] and rescaled.  The cost is
   [1/(weight d - mu d Q)], i.e., the inverse acceptance probability. *)
lemma adv_rdiv_inf_dexcepted (A <: Dist) (P : out_t -> bool) &m
                             (d : in_t distr) (Q : in_t -> bool) :
  mu d Q < weight d =>
  Pr[Sample(A).main(d \ Q) @ &m : P res] <=
    (1%r / (weight d - mu d Q)) * Pr[Sample(A).main(d) @ &m : P res].
proof.
move => lt_Q; apply (adv_rdiv_inf_le A P &m (1%r / (weight d - mu d Q))).
- exact dominated_dexcepted.
- exact rdiv_inf_dexcepted.
qed.

(* Sampling conditioned on [Q]: the adversary sees a sample from [dcond].
   Cost is [1/mu d Q] — inverse conditioning probability. *)
lemma adv_rdiv_inf_dcond (A <: Dist) (P : out_t -> bool) &m
                         (d : in_t distr) (Q : in_t -> bool) :
  0%r < mu d Q =>
  Pr[Sample(A).main(dcond d Q) @ &m : P res] <=
    (1%r / mu d Q) * Pr[Sample(A).main(d) @ &m : P res].
proof.
move => pos_Q; apply (adv_rdiv_inf_le A P &m (1%r / mu d Q)).
- exact dominated_dcond.
- exact rdiv_inf_dcond.
qed.

end Distinguisher.

(* Pre-composed dlist bound.  [dlist] fixes the sample type to a list,
   so it lives in a separate sub-theory that clones [Distinguisher] at
   [in_t <- t list]. *)
abstract theory DistinguisherList.
type t, out_t.

clone import Distinguisher as DL with
  type in_t <- t list,
  type out_t <- out_t
  proof*.

lemma adv_rdiv_inf_dlist (A <: DL.Dist) (P : out_t -> bool) &m
                         (M : real) (d1 d2 : t distr) n :
  0 <= n => dominated M d1 d2 =>
  Pr[DL.Sample(A).main(dlist d1 n) @ &m : P res] <=
    RField.exp (rdiv_inf d1 d2) n
    * Pr[DL.Sample(A).main(dlist d2 n) @ &m : P res].
proof.
move => ge0_n dom.
apply (DL.adv_rdiv_inf_le A P &m (RField.exp M n)).
- exact (dominated_dlist M).
- exact (rdiv_inf_dlist M).
qed.

end DistinguisherList.
