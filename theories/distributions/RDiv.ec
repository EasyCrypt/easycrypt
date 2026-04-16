require import AllCore List Distr DProd DList Dexcepted StdBigop StdOrder RealFLub.
(*---*) import Bigreal RealSeries RealOrder RField BRA.

(* ==========================================================================

   Rényi divergence — max-divergence (α = ∞).

   For subdistributions [d1], [d2], the max-divergence is the supremum of
   the pointwise Radon–Nikodym derivative:

     rdiv_inf d1 d2 = sup_x (mu1 d1 x / mu1 d2 x).

   Its flagship property is *probability preservation*: for any event [E],

     mu d1 E <= rdiv_inf d1 d2 * mu d2 E.

   The definition is only meaningful when the ratio is bounded — otherwise
   the supremum escapes to +∞, which we cannot represent.  We package the
   finite-bound requirement in the predicate [dominated d1 d2], stronger
   than classical absolute continuity: it asserts the existence of a
   *finite* constant [M] with [mu1 d1 x <= M * mu1 d2 x] pointwise.  Under
   [dominated d1 d2] every lemma below goes through; without it the
   [flub]-definition is unspecified and the lemmas are unprovable.

   Design notes (see .claude/pull-requests/rdiv.md for rationale):
   - Distributions are universally quantified in lemma statements, not
     fixed as theory-level ops.  This avoids the clone-per-call-site cost
     of [SDist.N1] / [SDist.ROM].
   - v1 is event-level only.  The distinguisher layer (section 4 in the
     SDist analogue) lives in a follow-up PR and will reuse
     [theories/query_counting/Counter.eca] for call counting.

   ========================================================================== *)

(* -- Dominance predicate --------------------------------------------------- *)

(* d1 is dominated by d2: the pointwise ratio is bounded by some constant.
   Equivalent to absolute continuity plus a bounded Radon–Nikodym derivative. *)
op dominated (d1 d2 : 'a distr) =
  exists M, 0%r <= M /\ forall x, mu1 d1 x <= M * mu1 d2 x.

(* -- Max-divergence -------------------------------------------------------- *)

op rdiv_inf (d1 d2 : 'a distr) =
  flub (fun x => mu1 d1 x / mu1 d2 x).

(* ==========================================================================
   Section 1 — dominance and basic bounds.
   ========================================================================== *)

lemma dominated_refl (d : 'a distr) : dominated d d.
proof. by exists 1%r; smt(ge0_mu1). qed.

lemma dominated_ac (d1 d2 : 'a distr) x :
  dominated d1 d2 => mu1 d2 x = 0%r => mu1 d1 x = 0%r.
proof.
case => M [_ le_mu1] mu2x_eq0.
have := le_mu1 x; rewrite mu2x_eq0 mulr0.
smt(ge0_mu1).
qed.

lemma has_fub_ratio (d1 d2 : 'a distr) :
  dominated d1 d2 => has_fub (fun x => mu1 d1 x / mu1 d2 x).
proof.
case => M [ge0_M le_mu1]; exists M => x /=.
case (mu1 d2 x = 0%r) => [-> | ne0].
- by rewrite invr0 mulr0.
- have pos : 0%r < mu1 d2 x by smt(ge0_mu1).
  by rewrite ler_pdivr_mulr //; apply le_mu1.
qed.

(* The defining sup form, exposed as a rewrite rule.  Fix (9). *)
lemma rdiv_infE (d1 d2 : 'a distr) :
  rdiv_inf d1 d2 = flub (fun x => mu1 d1 x / mu1 d2 x).
proof. by []. qed.

lemma rdiv_inf_upper_bound (d1 d2 : 'a distr) x :
  dominated d1 d2 => mu1 d1 x <= rdiv_inf d1 d2 * mu1 d2 x.
proof.
move => dom.
have hf := has_fub_ratio _ _ dom.
have ratio_le : mu1 d1 x / mu1 d2 x <= rdiv_inf d1 d2.
  by apply (flub_upper_bound<:'a> (fun x => mu1 d1 x / mu1 d2 x) x).
case (mu1 d2 x = 0%r) => [eq0 | ne0].
- by rewrite eq0 mulr0 (dominated_ac _ _ _ dom eq0).
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

lemma rdiv_inf_ge0 (d1 d2 : 'a distr) :
  dominated d1 d2 => 0%r <= rdiv_inf d1 d2.
proof.
move => dom; case: dom => M [ge0_M le_mu1].
have hf : has_fub (fun x => mu1 d1 x / mu1 d2 x) by apply has_fub_ratio; exists M.
(* Every value of the ratio is >= 0; pick [witness]. *)
apply (ler_trans (mu1 d1 witness / mu1 d2 witness)); last first.
- by apply (flub_upper_bound<:'a> (fun x => mu1 d1 x / mu1 d2 x) witness).
smt(ge0_mu1 invr_ge0 mulr_ge0).
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
by apply has_fub_ratio; exact dominated_refl.
qed.

(* dnull case. *)
lemma rdiv_inf_dnull (d : 'a distr) :
  rdiv_inf dnull<:'a> d = 0%r.
proof.
apply ler_anti; split => [|_].
- by apply rdiv_inf_le_ub => // x; rewrite mul0r dnull1E.
apply rdiv_inf_ge0; exists 0%r; split => // x.
by rewrite mul0r dnull1E.
qed.

(* ==========================================================================
   Section 2 — probability preservation.
   ========================================================================== *)

lemma rdiv_inf_pr (d1 d2 : 'a distr) E :
  dominated d1 d2 => mu d1 E <= rdiv_inf d1 d2 * mu d2 E.
proof.
move => dom.
have ge0_rdiv : 0%r <= rdiv_inf d1 d2 by exact rdiv_inf_ge0.
rewrite muE (muE d2) -sumZ.
apply ler_sum => [x /= | |].
- case (E x) => _; last by rewrite mulr0.
  exact (rdiv_inf_upper_bound _ _ _ dom).
- exact/summable_cond/summable_mu1.
- apply (summable_le_pos _ (fun x => rdiv_inf d1 d2 * mu1 d2 x)) => /=.
  + exact/summableZ/summable_mu1.
  move => x; case (E x) => _; smt(ge0_mu1 mulr_ge0).
qed.

(* ==========================================================================
   Section 3 — data-processing and composition.

   All bounds here are consequences of the pointwise upper bound:
     mu1 d1 x <= rdiv_inf d1 d2 * mu1 d2 x
   applied to the appropriate event or sum.  The pattern is:

     1. Prove [dominated (d1 ◇ e) (d2 ◇ e)] with witness [rdiv_inf d1 d2]
        (the sharp bound — this is where the real content lives).
     2. Conclude [rdiv_inf (d1 ◇ e) (d2 ◇ e) <= rdiv_inf d1 d2] by
        [rdiv_inf_le_ub].

   The "dominated" lemma is reusable (e.g., for chained compositions);
   the "rdiv_inf" lemma is what users usually cite.
   ========================================================================== *)

(* -- dmap ------------------------------------------------------------------ *)

lemma dominated_dmap (d1 d2 : 'a distr) (F : 'a -> 'b) :
  dominated d1 d2 => dominated (dmap d1 F) (dmap d2 F).
proof.
move => dom.
exists (rdiv_inf d1 d2); split; first exact rdiv_inf_ge0.
move => b; rewrite !dmap1E.
exact (rdiv_inf_pr _ _ _ dom).
qed.

lemma rdiv_inf_dmap (d1 d2 : 'a distr) (F : 'a -> 'b) :
  dominated d1 d2 => rdiv_inf (dmap d1 F) (dmap d2 F) <= rdiv_inf d1 d2.
proof.
move => dom.
apply rdiv_inf_le_ub; first exact rdiv_inf_ge0.
move => b; rewrite !dmap1E.
exact (rdiv_inf_pr _ _ _ dom).
qed.

(* -- dlet ------------------------------------------------------------------ *)

(* Pointwise upper bound for [dlet].  Shared by [dominated_dlet] and
   [rdiv_inf_dlet]. *)
lemma dlet_pointwise (d1 d2 : 'a distr) (F : 'a -> 'b distr) y :
  dominated d1 d2 =>
  mu1 (dlet d1 F) y <= rdiv_inf d1 d2 * mu1 (dlet d2 F) y.
proof.
move => dom; rewrite !dlet1E -sumZ.
apply ler_sum => [x /= | |].
- rewrite mulrA; apply ler_wpmul2r; first exact ge0_mu1.
  exact (rdiv_inf_upper_bound _ _ _ dom).
- by apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
- apply summableZ; apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
qed.

lemma dominated_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) :
  dominated d1 d2 => dominated (dlet d1 F) (dlet d2 F).
proof.
move => dom; exists (rdiv_inf d1 d2); split; first exact rdiv_inf_ge0.
by move => y; apply dlet_pointwise.
qed.

lemma rdiv_inf_dlet (d1 d2 : 'a distr) (F : 'a -> 'b distr) :
  dominated d1 d2 => rdiv_inf (dlet d1 F) (dlet d2 F) <= rdiv_inf d1 d2.
proof.
move => dom; apply rdiv_inf_le_ub; first exact rdiv_inf_ge0.
by move => y; apply dlet_pointwise.
qed.

(* -- dprod ----------------------------------------------------------------- *)

lemma dprod_pointwise (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) p :
  dominated dl1 dl2 => dominated dr1 dr2 =>
  mu1 (dl1 `*` dr1) p <= rdiv_inf dl1 dl2 * rdiv_inf dr1 dr2 * mu1 (dl2 `*` dr2) p.
proof.
move => doml domr; case: p => a b; rewrite !dprod1E.
have -> :
  rdiv_inf dl1 dl2 * rdiv_inf dr1 dr2 * (mu1 dl2 a * mu1 dr2 b)
  = (rdiv_inf dl1 dl2 * mu1 dl2 a) * (rdiv_inf dr1 dr2 * mu1 dr2 b) by ring.
by apply ler_pmul; smt(ge0_mu1 rdiv_inf_upper_bound).
qed.

lemma dominated_dprod (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  dominated dl1 dl2 => dominated dr1 dr2 =>
  dominated (dl1 `*` dr1) (dl2 `*` dr2).
proof.
move => doml domr.
exists (rdiv_inf dl1 dl2 * rdiv_inf dr1 dr2); split.
- by smt(mulr_ge0 rdiv_inf_ge0).
by move => p; apply dprod_pointwise.
qed.

lemma rdiv_inf_dprod (dl1 dl2 : 'a distr) (dr1 dr2 : 'b distr) :
  dominated dl1 dl2 => dominated dr1 dr2 =>
  rdiv_inf (dl1 `*` dr1) (dl2 `*` dr2) <= rdiv_inf dl1 dl2 * rdiv_inf dr1 dr2.
proof.
move => doml domr.
apply rdiv_inf_le_ub; first by smt(mulr_ge0 rdiv_inf_ge0).
by move => p; apply dprod_pointwise.
qed.

(* -- dlist ----------------------------------------------------------------- *)

lemma dominated_dlist (d1 d2 : 'a distr) n :
  0 <= n => dominated d1 d2 =>
  dominated (dlist d1 n) (dlist d2 n).
proof.
move => ge0_n dom; elim: n ge0_n => [|n ge0_n IHn].
- by rewrite !dlist0 //; exact dominated_refl.
rewrite !dlistS //.
apply dominated_dmap.
by apply dominated_dprod; [exact dom | exact IHn].
qed.

lemma rdiv_inf_dlist (d1 d2 : 'a distr) n :
  0 <= n => dominated d1 d2 =>
  rdiv_inf (dlist d1 n) (dlist d2 n) <= RField.exp (rdiv_inf d1 d2) n.
proof.
move => ge0_n dom.
have ge0_rdiv : 0%r <= rdiv_inf d1 d2 by exact rdiv_inf_ge0.
elim: n ge0_n => [|n ge0_n IHn].
- rewrite !dlist0 // RField.expr0 rdiv_inf_dd //.
  by rewrite dunit_ll.
rewrite !dlistS // RField.exprS //.
apply (ler_trans (rdiv_inf (d1 `*` dlist d1 n) (d2 `*` dlist d2 n))).
- by apply rdiv_inf_dmap; apply dominated_dprod => //;
     exact (dominated_dlist _ _ _ ge0_n dom).
apply (ler_trans (rdiv_inf d1 d2 * rdiv_inf (dlist d1 n) (dlist d2 n))).
- by apply rdiv_inf_dprod => //; exact (dominated_dlist _ _ _ ge0_n dom).
by apply ler_wpmul2l.
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
  dominated (d \ P) d.
proof.
move => lt_P.
pose M := 1%r / (weight d - mu d P).
have pos_wP : 0%r < weight d - mu d P by smt().
have ge0_M : 0%r <= M by rewrite /M; smt(invr_gt0).
exists M; split => // x; rewrite dexcepted1E.
case (P x) => _.
- by rewrite /M; smt(ge0_mu1 mulr_ge0 invr_gt0).
by rewrite /M; smt(ge0_mu1).
qed.

lemma rdiv_inf_dexcepted (d : 'a distr) (P : 'a -> bool) :
  mu d P < weight d =>
  rdiv_inf (d \ P) d <= 1%r / (weight d - mu d P).
proof.
move => lt_P.
have pos_wP : 0%r < weight d - mu d P by smt().
apply rdiv_inf_le_ub; first by smt(invr_gt0).
move => x; rewrite dexcepted1E.
case (P x) => _; smt(ge0_mu1 mulr_ge0 invr_gt0).
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
  dominated (drestrict d P) d.
proof.
exists 1%r; split => // x; rewrite drestrict1E mul1r.
by case (P x) => _; smt(ge0_mu1).
qed.

lemma rdiv_inf_drestrict (d : 'a distr) (P : 'a -> bool) :
  rdiv_inf (drestrict d P) d <= 1%r.
proof.
apply rdiv_inf_le_ub => // x; rewrite drestrict1E mul1r.
by case (P x) => _; smt(ge0_mu1).
qed.

(* [dcond d P = dscale (drestrict d P)]: condition on [P] (normalize).
   Equivalent to [d \ (predC P)]. *)
lemma dominated_dcond (d : 'a distr) (P : 'a -> bool) :
  0%r < mu d P =>
  dominated (dcond d P) d.
proof.
move => pos_P.
pose M := 1%r / mu d P.
have ge0_M : 0%r <= M by rewrite /M; smt(invr_gt0).
exists M; split => // x; rewrite dcond1E.
case (P x) => _.
- by rewrite /M; smt(ge0_mu1 mulr_ge0 invr_gt0).
by rewrite /M; smt(ge0_mu1 mulr_ge0).
qed.

lemma rdiv_inf_dcond (d : 'a distr) (P : 'a -> bool) :
  0%r < mu d P =>
  rdiv_inf (dcond d P) d <= 1%r / mu d P.
proof.
move => pos_P.
apply rdiv_inf_le_ub; first by smt(invr_gt0).
move => x; rewrite dcond1E.
case (P x) => _; smt(ge0_mu1 mulr_ge0 invr_gt0).
qed.

(* -- djoinmap -------------------------------------------------------------

   [djoinmap F xs = djoin (map F xs)]: the heterogeneous product of a list
   of distributions indexed by [xs].  Generalizes [dlist] (which is the
   homogeneous case).  The Rényi cost multiplies across indices. *)
lemma dominated_djoinmap ['a 'b] (F1 F2 : 'a -> 'b distr) (xs : 'a list) :
  (forall x, x \in xs => dominated (F1 x) (F2 x)) =>
  dominated (djoinmap F1 xs) (djoinmap F2 xs).
proof.
elim: xs => [_|x xs IHxs dom_cons].
- rewrite /djoinmap /=; exact dominated_refl.
have dom_head : dominated (F1 x) (F2 x) by apply dom_cons; rewrite mem_head.
have dom_tail : dominated (djoinmap F1 xs) (djoinmap F2 xs).
- by apply IHxs => y y_in; apply dom_cons; rewrite in_cons y_in.
rewrite /djoinmap /= !djoin_cons.
apply dominated_dmap.
exact (dominated_dprod _ _ _ _ dom_head dom_tail).
qed.

lemma rdiv_inf_djoinmap ['a 'b] (F1 F2 : 'a -> 'b distr) (xs : 'a list) :
  (forall x, x \in xs => dominated (F1 x) (F2 x)) =>
  rdiv_inf (djoinmap F1 xs) (djoinmap F2 xs) <=
    BRM.big predT (fun x => rdiv_inf (F1 x) (F2 x)) xs.
proof.
elim: xs => [_|x xs IHxs dom_cons].
- rewrite /djoinmap /= djoin_nil BRM.big_nil.
  by apply rdiv_inf_le_ub => // y; rewrite mul1r.
have dom_head : dominated (F1 x) (F2 x) by apply dom_cons; rewrite mem_head.
have dom_tail_all : forall y, y \in xs => dominated (F1 y) (F2 y).
- by move => y y_in; apply dom_cons; rewrite in_cons y_in.
have dom_tail : dominated (djoinmap F1 xs) (djoinmap F2 xs)
  by apply dominated_djoinmap.
have ge0_head : 0%r <= rdiv_inf (F1 x) (F2 x) by exact rdiv_inf_ge0.
have ge0_tail_rdiv : 0%r <= rdiv_inf (djoinmap F1 xs) (djoinmap F2 xs)
  by exact rdiv_inf_ge0.
rewrite /djoinmap /= !djoin_cons BRM.big_cons /predT /=.
apply (ler_trans
  (rdiv_inf (F1 x `*` djoinmap F1 xs) (F2 x `*` djoinmap F2 xs))).
- by apply rdiv_inf_dmap;
     apply (dominated_dprod _ _ _ _ dom_head dom_tail).
apply (ler_trans
  (rdiv_inf (F1 x) (F2 x) * rdiv_inf (djoinmap F1 xs) (djoinmap F2 xs))).
- exact (rdiv_inf_dprod _ _ _ _ dom_head dom_tail).
by apply ler_wpmul2l => //; apply IHxs.
qed.

(* -- djoin ----------------------------------------------------------------

   [djoin (ds : 'a distr list) : 'a list distr] is the heterogeneous
   product of a list of distributions.  One-line corollary of djoinmap
   via the identity realization. *)

lemma djoinmap_nth ['a] (ds : 'a distr list) :
  djoinmap (fun i => nth witness ds i) (range 0 (size ds)) = djoin ds.
proof. by congr; apply map_nth_range. qed.

lemma dominated_djoin ['a] (ds1 ds2 : 'a distr list) :
  size ds1 = size ds2 =>
  (forall i, 0 <= i < size ds1 =>
     dominated (nth witness ds1 i) (nth witness ds2 i)) =>
  dominated (djoin ds1) (djoin ds2).
proof.
move => eq_sz dom_i.
rewrite -(djoinmap_nth ds1) -(djoinmap_nth ds2) -eq_sz.
apply dominated_djoinmap => i; rewrite mem_range => rng_i.
exact (dom_i i rng_i).
qed.

lemma rdiv_inf_djoin ['a] (ds1 ds2 : 'a distr list) :
  size ds1 = size ds2 =>
  (forall i, 0 <= i < size ds1 =>
     dominated (nth witness ds1 i) (nth witness ds2 i)) =>
  rdiv_inf (djoin ds1) (djoin ds2) <=
    BRM.big predT (fun i => rdiv_inf (nth witness ds1 i) (nth witness ds2 i))
                   (range 0 (size ds1)).
proof.
move => eq_sz dom_i.
rewrite -(djoinmap_nth ds1) -(djoinmap_nth ds2) -eq_sz.
apply rdiv_inf_djoinmap => i; rewrite mem_range => rng_i.
exact (dom_i i rng_i).
qed.

(* -- dfst / dsnd ---------------------------------------------------------

   Marginals of a pair distribution.  Trivially follows from dmap. *)

lemma dominated_dfst ['a 'b] (d1 d2 : ('a * 'b) distr) :
  dominated d1 d2 => dominated (dfst d1) (dfst d2).
proof. exact (dominated_dmap _ _ fst). qed.

lemma rdiv_inf_dfst ['a 'b] (d1 d2 : ('a * 'b) distr) :
  dominated d1 d2 => rdiv_inf (dfst d1) (dfst d2) <= rdiv_inf d1 d2.
proof. exact (rdiv_inf_dmap _ _ fst). qed.

lemma dominated_dsnd ['a 'b] (d1 d2 : ('a * 'b) distr) :
  dominated d1 d2 => dominated (dsnd d1) (dsnd d2).
proof. exact (dominated_dmap _ _ snd). qed.

lemma rdiv_inf_dsnd ['a 'b] (d1 d2 : ('a * 'b) distr) :
  dominated d1 d2 => rdiv_inf (dsnd d1) (dsnd d2) <= rdiv_inf d1 d2.
proof. exact (rdiv_inf_dmap _ _ snd). qed.

(* -- dopt ----------------------------------------------------------------

   [dopt d : 'a option distr] adds a [None] branch with the remaining
   mass [1 - weight d].  If [d1] and [d2] have equal weights, [dopt]
   preserves dominance with the same bound. *)

lemma dominated_dopt (d1 d2 : 'a distr) :
  weight d1 = weight d2 =>
  dominated d1 d2 =>
  dominated (dopt d1) (dopt d2).
proof.
move => eq_w dom.
have ge0_rdiv : 0%r <= rdiv_inf d1 d2 by exact rdiv_inf_ge0.
exists (maxr 1%r (rdiv_inf d1 d2)); split; first smt().
case => [|y]; rewrite !dopt1E /=.
- by rewrite eq_w; smt(mu_bounded).
apply (ler_trans (rdiv_inf d1 d2 * mu1 d2 y)); first exact rdiv_inf_upper_bound.
apply ler_wpmul2r; smt(ge0_mu1).
qed.

lemma rdiv_inf_dopt (d1 d2 : 'a distr) :
  weight d1 = weight d2 =>
  dominated d1 d2 =>
  rdiv_inf (dopt d1) (dopt d2) <= maxr 1%r (rdiv_inf d1 d2).
proof.
move => eq_w dom.
have ge0_rdiv : 0%r <= rdiv_inf d1 d2 by exact rdiv_inf_ge0.
apply rdiv_inf_le_ub; first smt().
case => [|y]; rewrite !dopt1E /=.
- by rewrite eq_w; smt(mu_bounded).
apply (ler_trans (rdiv_inf d1 d2 * mu1 d2 y)); first exact rdiv_inf_upper_bound.
apply ler_wpmul2r; smt(ge0_mu1).
qed.

(* -- Bilinear dlet dominance ----------------------------------------------

   Strengthens [dominated_dlet] to allow the kernel to differ between the
   two sides, at the cost of a *uniform* pointwise bound on the kernel
   (a single constant [MF] works for every [x]). *)

lemma dominated_dlet' ['a 'b] (d1 d2 : 'a distr) (F1 F2 : 'a -> 'b distr) :
  dominated d1 d2 =>
  (exists M, 0%r <= M /\ forall x y, mu1 (F1 x) y <= M * mu1 (F2 x) y) =>
  dominated (dlet d1 F1) (dlet d2 F2).
proof.
case => M_d [ge0_Md dom_d] [M_F [ge0_MF dom_F]].
exists (M_d * M_F); split; first smt(mulr_ge0).
move => y; rewrite !dlet1E -sumZ.
apply ler_sum => [x /= | |].
- have h1 := dom_d x.
  have h2 := dom_F x y.
  have : mu1 d1 x * mu1 (F1 x) y <= (M_d * mu1 d2 x) * (M_F * mu1 (F2 x) y).
  + by apply ler_pmul; smt(ge0_mu1).
  smt().
- apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
- apply summableZ; apply summable_mu1_wght => x; smt(ge0_mu1 le1_mu1).
qed.

(* -- dfold ---------------------------------------------------------------

   [dfold f x n] iterates [f] for [n] steps starting from [x].  Analogue
   of [dlist] for state-carrying iteration.  The Rényi cost composes
   multiplicatively over the loop. *)

(* Dominance of [dfold] under step-wise uniform domination.  The uniform
   quantifier over the accumulator [y] matches [dominated_dlet']'s shape. *)
lemma dominated_dfold ['a] (f1 f2 : int -> 'a -> 'a distr) (x : 'a) (n : int) :
  0 <= n =>
  (forall i, 0 <= i < n =>
     exists M, 0%r <= M /\ forall y z, mu1 (f1 i y) z <= M * mu1 (f2 i y) z) =>
  dominated (dfold f1 x n) (dfold f2 x n).
proof.
move => ge0_n; elim: n ge0_n => [|n ge0_n IHn] step.
- by rewrite !dfold0; exact dominated_refl.
rewrite !dfoldS //.
apply dominated_dlet'.
- by apply IHn => i rng_i; apply step; smt().
by apply (step n); smt().
qed.

(* rdiv_inf bound for dfold.  User supplies per-step bound [Ms i] that
   uniformly dominates the i-th step's kernel.  Conclusion: rdiv_inf is
   bounded by the product of step-wise bounds. *)
lemma rdiv_inf_dfold ['a] (f1 f2 : int -> 'a -> 'a distr) (x : 'a) (n : int)
      (Ms : int -> real) :
  0 <= n =>
  (forall i, 0 <= i < n =>
     0%r <= Ms i /\ forall y z, mu1 (f1 i y) z <= Ms i * mu1 (f2 i y) z) =>
  rdiv_inf (dfold f1 x n) (dfold f2 x n) <= BRM.big predT Ms (range 0 n).
proof.
(* Helper: product over a range is nonneg when each factor is. *)
have prod_range_ge0 : forall (k : int) (g : int -> real),
  (forall i, i \in range 0 k => 0%r <= g i) =>
  0%r <= BRM.big predT g (range 0 k).
- move => k g h_pos.
  elim: (range 0 k) h_pos => [_|h t IHt h_pos]; first by rewrite BRM.big_nil.
  rewrite BRM.big_cons {1}/predT /=.
  apply mulr_ge0; first by apply h_pos; rewrite mem_head.
  by apply IHt => i i_in; apply h_pos; rewrite in_cons i_in.
(* Main induction. *)
move => ge0_n; elim: n ge0_n => [|n ge0_n IHn] step.
- rewrite !dfold0 range_geq // BRM.big_nil.
  by apply rdiv_inf_le_ub => // y; rewrite mul1r.
rewrite !dfoldS // BRM.big_int_recr //.
apply rdiv_inf_le_ub.
- apply mulr_ge0.
  + apply prod_range_ge0 => i /mem_range rng_i.
    by have := step i _; smt().
  + by have := step n _; smt().
move => y; rewrite !dlet1E -sumZ.
apply ler_sum => [z /= | |].
- have dom_f : mu1 (dfold f1 x n) z <=
               BRM.big predT Ms (range 0 n) * mu1 (dfold f2 x n) z.
  + apply (ler_trans (rdiv_inf (dfold f1 x n) (dfold f2 x n) * mu1 (dfold f2 x n) z)).
    * apply rdiv_inf_upper_bound.
      apply dominated_dfold => // i rng_i.
      by exists (Ms i); apply step; smt().
    apply ler_wpmul2r; first exact ge0_mu1.
    by apply IHn => i rng_i; apply step; smt().
  have dom_step : mu1 (f1 n z) y <= Ms n * mu1 (f2 n z) y by smt().
  have : mu1 (dfold f1 x n) z * mu1 (f1 n z) y <=
         (BRM.big predT Ms (range 0 n) * mu1 (dfold f2 x n) z) *
         (Ms n * mu1 (f2 n z) y).
  + by apply ler_pmul; smt(ge0_mu1).
  smt().
- apply summable_mu1_wght => z; smt(ge0_mu1 le1_mu1).
- apply summableZ; apply summable_mu1_wght => z; smt(ge0_mu1 le1_mu1).
qed.

(* -- dfun ----------------------------------------------------------------

   [dfun F : (t -> 'u) distr] samples a function over a finite domain
   [t] by sampling [F x] at each point independently.  Rényi multiplies
   across the domain.  [dfun] is only defined inside a finite-type
   context, so we stage it in an abstract sub-theory that clones
   [MUniFinFun] to obtain the finite type and operators. *)

abstract theory RDivFun.
  clone import MUniFinFun.

  lemma dominated_dfun ['u] (F1 F2 : t -> 'u distr) :
    (forall x, dominated (F1 x) (F2 x)) =>
    dominated (dfun F1) (dfun F2).
  proof.
  move => dom_pt.
  rewrite !dfun_dmap.
  apply dominated_dmap.
  apply dominated_djoinmap => x _; exact (dom_pt x).
  qed.

  lemma rdiv_inf_dfun ['u] (F1 F2 : t -> 'u distr) :
    (forall x, dominated (F1 x) (F2 x)) =>
    rdiv_inf (dfun F1) (dfun F2) <=
      BRM.big predT (fun x => rdiv_inf (F1 x) (F2 x)) FinT.enum.
  proof.
  move => dom_pt.
  rewrite !dfun_dmap.
  apply (ler_trans (rdiv_inf (djoinmap F1 FinT.enum) (djoinmap F2 FinT.enum))).
  - apply rdiv_inf_dmap.
    apply dominated_djoinmap => x _; exact (dom_pt x).
  apply rdiv_inf_djoinmap => x _; exact (dom_pt x).
  qed.

end RDivFun.

(* ==========================================================================
   Section 4 — Distinguisher layer.

   Lifts probability preservation from events to adversaries.  The main
   lemma [adv_rdiv_inf] says:

     Pr[Sample(A).main(d1) @ &m : P res]
       <= rdiv_inf d1 d2 * Pr[Sample(A).main(d2) @ &m : P res].

   Design (see .claude/pull-requests/rdiv.md):
   - Generic output type [out_t] — no bool specialization (SDist fix 3).
   - Distributions as [main] arguments, not fixed ops (SDist fix 2).
   - [adv_rdiv_inf] takes the pRHL judgment directly, no reshape (fix 8).
   ========================================================================== *)

require DProd.

abstract theory Distinguisher.
type in_t, out_t.

module type Dist = {
  proc guess(x : in_t) : out_t
}.

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

(* Elementary sampler, used to encode [A.guess]'s per-input output
   distribution as a first-class distr. *)
module S = {
  proc sample (d : out_t distr) = {
    var r;

    r <$ d;
    return r;
  }
}.

lemma sampleE (d' : out_t distr) &m a :
  Pr[S.sample(d') @ &m : res = a] = mu1 d' a.
proof. by byphoare (: d = d' ==> _) => //; proc; rnd; auto. qed.

(* The per-input adversary output distribution is well-formed. *)
lemma uniq_big_res (A <: Dist) &m x' (zs : out_t list) :
  uniq zs =>
  big predT (fun z => Pr[A.guess(x') @ &m : res = z]) zs =
  Pr[A.guess(x') @ &m : res \in zs].
proof.
elim: zs => [_|z zs IHzs /= [zNzs uq_zs]].
- by rewrite big_nil; byphoare => //; hoare; auto.
by rewrite big_cons {1}/predT /= IHzs // Pr[mu_disjoint] /#.
qed.

lemma adv_isdistr (A <: Dist) &m x' :
  isdistr (fun z => Pr[A.guess(x') @ &m : res = z]).
proof.
split => [z /=|zs uq_zs]; first by byphoare.
by rewrite (uniq_big_res A &m) //; byphoare.
qed.

lemma adv_mu1 (A <: Dist) &m x' z :
  Pr[A.guess(x') @ &m : res = z] =
  mu1 (mk (fun z' => Pr[A.guess(x') @ &m : res = z'])) z.
proof. by rewrite muK //; exact (adv_isdistr A &m x'). qed.

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
lemma adv_rdiv_inf (A <: Dist) (P : out_t -> bool) &m (d1 d2 : in_t distr) :
  dominated d1 d2 =>
  Pr[Sample(A).main(d1) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(d2) @ &m : P res].
proof.
move => dom.
rewrite !(Sample_dletE A).
pose F := fun x => mk (fun z => Pr[A.guess(x) @ &m : res = z]).
apply (ler_trans (rdiv_inf (dlet d1 F) (dlet d2 F) * mu (dlet d2 F) P)).
- exact (rdiv_inf_pr _ _ P (dominated_dlet _ _ F dom)).
apply ler_wpmul2r; first exact ge0_mu.
exact (rdiv_inf_dlet _ _ F dom).
qed.

(* -- Pre-composed adversary bounds ----------------------------------------

   Fuse [adv_rdiv_inf] with the structural lemmas so users cite a single
   composed result instead of chaining three applications.  Each saves one
   ler_trans hop and one explicit module argument per call site.  *)

lemma adv_rdiv_inf_dmap ['a] (A <: Dist) (P : out_t -> bool) &m
                        (G : 'a -> in_t) (d1 d2 : 'a distr) :
  dominated d1 d2 =>
  Pr[Sample(A).main(dmap d1 G) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(dmap d2 G) @ &m : P res].
proof.
move => dom.
apply (ler_trans
  (rdiv_inf (dmap d1 G) (dmap d2 G) * Pr[Sample(A).main(dmap d2 G) @ &m : P res])).
- by apply (adv_rdiv_inf A); apply dominated_dmap.
apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
exact (rdiv_inf_dmap _ _ G dom).
qed.

lemma adv_rdiv_inf_dlet ['a] (A <: Dist) (P : out_t -> bool) &m
                        (G : 'a -> in_t distr) (d1 d2 : 'a distr) :
  dominated d1 d2 =>
  Pr[Sample(A).main(dlet d1 G) @ &m : P res] <=
    rdiv_inf d1 d2 * Pr[Sample(A).main(dlet d2 G) @ &m : P res].
proof.
move => dom.
apply (ler_trans
  (rdiv_inf (dlet d1 G) (dlet d2 G) * Pr[Sample(A).main(dlet d2 G) @ &m : P res])).
- by apply (adv_rdiv_inf A); apply dominated_dlet.
apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
exact (rdiv_inf_dlet _ _ G dom).
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
move => lt_Q.
apply (ler_trans
  (rdiv_inf (d \ Q) d * Pr[Sample(A).main(d) @ &m : P res])).
- by apply (adv_rdiv_inf A); apply dominated_dexcepted.
apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
exact (rdiv_inf_dexcepted _ _ lt_Q).
qed.

(* Sampling conditioned on [Q]: the adversary sees a sample from [dcond].
   Cost is [1/mu d Q] — inverse conditioning probability. *)
lemma adv_rdiv_inf_dcond (A <: Dist) (P : out_t -> bool) &m
                         (d : in_t distr) (Q : in_t -> bool) :
  0%r < mu d Q =>
  Pr[Sample(A).main(dcond d Q) @ &m : P res] <=
    (1%r / mu d Q) * Pr[Sample(A).main(d) @ &m : P res].
proof.
move => pos_Q.
apply (ler_trans
  (rdiv_inf (dcond d Q) d * Pr[Sample(A).main(d) @ &m : P res])).
- by apply (adv_rdiv_inf A); apply dominated_dcond.
apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
exact (rdiv_inf_dcond _ _ pos_Q).
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
                         (d1 d2 : t distr) n :
  0 <= n => dominated d1 d2 =>
  Pr[DL.Sample(A).main(dlist d1 n) @ &m : P res] <=
    RField.exp (rdiv_inf d1 d2) n
    * Pr[DL.Sample(A).main(dlist d2 n) @ &m : P res].
proof.
move => ge0_n dom.
apply (ler_trans
  (rdiv_inf (dlist d1 n) (dlist d2 n)
   * Pr[DL.Sample(A).main(dlist d2 n) @ &m : P res])).
- by apply (DL.adv_rdiv_inf A); apply dominated_dlist.
apply ler_wpmul2r; first by rewrite Pr [mu_ge0].
exact (rdiv_inf_dlist _ _ _ ge0_n dom).
qed.

end DistinguisherList.
