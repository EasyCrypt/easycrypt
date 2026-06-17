(* ==========================================================================

   Rényi-∞ oracle bound for bounded-query sequential adversaries,
   PARAMETRIC over a shared parameter [p : param_t].  The parameter is
   NOT hidden from the adversary: the games pass [p] to [A.main] in the
   clear (the bound holds a fortiori for parameter-aware adversaries).

   User-facing lemma [rdiv_bound_sampler] concludes, for any event
   [E : bool -> bool] and any A that makes at most N sampler queries
   ([A_bound1]/[A_bound2]) and is lossless whenever its oracle is
   ([A_ll]):

     Pr[Game1(A).main @ &m : E res] <= M ^ N * Pr[Game2(A).main @ &m : E res]

   where:
   - [Game_i] samples [p <$ d_param], sets [Sampler_i.p := p], then runs A.
   - [Sampler_i.get] returns a fresh draw from [d_i p] for every [p] the
     game can draw (its literal kernel is the classically totalized
     [dtot_i], equal to [d_i] on [supp d_param] — see the plumbing note).
   - [M] is an explicit uniform dominance witness:
       forall p ∈ supp d_param, forall x, mu1 (d1 p) x ≤ M * mu1 (d2 p) x.
   - [N] is A's query budget.
   All per-parameter hypotheses ([d_i_ll], dominance) are required only on
   [supp d_param]; restricting to a subset of good parameters is done by
   conditioning [d_param] ([RDivOracleValid] packages exactly that).

   Non-parametric specialization:
     [param_t := unit, d_param := dunit (), d1 := fun _ => d, d2 := fun _ => d'].

   ARCHITECTURE: presampling is fully delegated to [BoundedPreSample.ec].
   BPS1, BPS2 (clones for d1, d2) provide the [eq_pr_fresh_ref_ev]
   Pr-equality between fresh-sampling and pre-sampled-list games.  Two
   clones share [Iface] (Oracle/Adv module types) so a single [A] applies.

   The internal chain routes through JOINT distributions — the per-p
   fresh≡ref equality cannot be lifted through the p-sampling directly:

       Game1(A)
          ≡ [Game1_eq_Joint1]
            (couple the p-draw; per-p [BPS1.eq_pr_fresh_ref_ev] via bypr)
       G_Joint1 — p <$ d_param; xs <$ dlist (dtot1 p) N; run A on BPS1.Ref
          ≡ [G_Joint1_vs_Sample]  (shape rename)
       Sample(B).main(joint1),
         joint1 = dlet d_param (fun p => dmap (dlist (dtot1 p) N)
                                              (fun xs => (p, xs)))

   (and mirrored on side 2 with 1 -> 2 in every name).  One
   [adv_rdiv_inf_le] application on the joints ([Joint_rdiv_bound]) closes
   the bound: [joint_pt_bound] gives [rdiv_inf joint1 joint2 <= M ^ N]
   pointwise, the [d_param] marginal cancelling in the ratio; the public
   [rdiv_bound_sampler] is the composition of the three steps.

   ========================================================================== *)

require import AllCore List Distr DList StdOrder StdBigop RealSeries.
require import RDiv.
require import BoundedPreSample.
(*---*) import RField RealOrder Bigreal.BRA.

abstract theory RDivOracle.

(* -- Parameters ----------------------------------------------------------- *)

type out_t.
type param_t.

(* Single Iface clone — both top-level access target (consumers use
   [RDO.Iface.Oracle]/[RDO.Iface.Adv]) and BPS substitution target.
   [<=] (inline-and-keep), not [<-]: the symbols must survive the clone
   because [theory Iface <- Iface] below matches BPS's own [Iface]
   structurally, and [<-] would clear the very names it matches on. *)
clone import BPS_Iface as Iface with
  type out_t   <= out_t,
  type param_t <= param_t.

op [lossless] d_param : param_t distr.

op d1 : param_t -> out_t distr.
op d2 : param_t -> out_t distr.

(* Per-parameter hypotheses are required only on the support of [d_param]
   — the parameters the games can actually draw.  Restricting the theorem
   to a subset of "good" parameters is therefore an *instantiation*:
   condition [d_param] (see [RDivOracleValid] below for the packaged
   valid-predicate surface). *)
axiom d1_ll : forall p, p \in d_param => is_lossless (d1 p).
axiom d2_ll : forall p, p \in d_param => is_lossless (d2 p).

op N : { int | 0 <= N } as N_ge0.
op M : { real | 0%r <= M } as M_ge0.

axiom d1_dominated_d2 :
  forall p, p \in d_param =>
    forall x, mu1 (d1 p) x <= M * mu1 (d2 p) x.

(* -- Internal plumbing: totalized kernels ---------------------------------
   BPS demands losslessness at EVERY parameter (its eager-sampling engine
   indexes a PROM by all (p, i) pairs), while [d1_ll]/[d2_ll] speak only
   about [supp d_param].  [dtot_i] bridges the gap classically, defaulting
   to [dunit witness] wherever [d_i] is lossy — which, by [d_i_ll], can
   only happen outside [supp d_param], where the games never sample.  On
   [supp d_param], [Sampler_i.get] draws exactly [d_i p]. *)
op dtot1 = fun p => if is_lossless (d1 p) then d1 p else dunit witness.
op dtot2 = fun p => if is_lossless (d2 p) then d2 p else dunit witness.

lemma dtot1_ll p : is_lossless (dtot1 p).
proof. by rewrite /dtot1; case (is_lossless (d1 p)) => // _; exact dunit_ll. qed.

lemma dtot2_ll p : is_lossless (dtot2 p).
proof. by rewrite /dtot2; case (is_lossless (d2 p)) => // _; exact dunit_ll. qed.

lemma dtot1E p : p \in d_param => dtot1 p = d1 p.
proof. by move => p_in; rewrite /dtot1 (d1_ll p p_in). qed.

lemma dtot2E p : p \in d_param => dtot2 p = d2 p.
proof. by move => p_in; rewrite /dtot2 (d2_ll p p_in). qed.

(* -- BoundedPreSample clones ---------------------------------------------- *)

clone BoundedPreSample as BPS1 with
  type out_t       <- out_t,
  type param_t     <- param_t,
  theory Iface     <- Iface,
  op    d          <- dtot1,
  op    N          <- N
  proof *.
realize d_ll  by exact dtot1_ll.
realize N_ge0 by exact N_ge0.

clone BoundedPreSample as BPS2 with
  type out_t       <- out_t,
  type param_t     <- param_t,
  theory Iface     <- Iface,
  op    d          <- dtot2,
  op    N          <- N
  proof *.
realize d_ll  by exact dtot2_ll.
realize N_ge0 by exact N_ge0.

(* -- Public surface ------------------------------------------------------- *)

(* Re-export BPS_i.Fresh (the fresh sampler) under the public-facing names. *)
module Sampler1 = BPS1.Fresh.
module Sampler2 = BPS2.Fresh.

module Game1 (A : Adv) = {
  proc main() : bool = {
    var p, r;
    p <$ d_param;
    Sampler1.p <- p;
    r <@ A(Sampler1).main(p);
    return r;
  }
}.

module Game2 (A : Adv) = {
  proc main() : bool = {
    var p, r;
    p <$ d_param;
    Sampler2.p <- p;
    r <@ A(Sampler2).main(p);
    return r;
  }
}.

(* -- Section: A, axioms, internal Rényi chain, user-facing lemma ----------

   MIRRORING.  Everything below comes in side-1/side-2 pairs (Game1/Game2,
   BPS1/BPS2, joint1/joint2, ...).  EC lemmas cannot abstract over which
   sampler *module* is in play (module types expose no state), so each
   side-2 proof is a verbatim mirror of its side-1 twin with 1 -> 2
   renamings.  Audit side 1; diff side 2 against it. *)

section.

declare module A <: Adv
  { -Sampler1, -Sampler2, -BPS1.Count, -BPS2.Count, -BPS1.Ref, -BPS2.Ref }.

declare axiom A_ll :
  forall (O <: Oracle { -A }),
    islossless O.get => islossless A(O).main.

declare axiom A_bound1 :
  hoare[ A(BPS1.Count(Sampler1)).main :
    BPS1.Count.n = 0 ==> BPS1.Count.n <= N ].

declare axiom A_bound2 :
  hoare[ A(BPS2.Count(Sampler2)).main :
    BPS2.Count.n = 0 ==> BPS2.Count.n <= N ].

(* Distinguisher clone for the joint Rényi step.  Inputs are pairs
   [(p, xs) : param_t * out_t list] so [B.guess] can install both [p]
   (passed as A's argument) and [xs] (consumed by [Ref]) in a single
   step — no out-of-band [Sampler.p] coupling needed. *)
local clone import Distinguisher as DistJoint with
  type in_t  <- param_t * out_t list,
  type out_t <- bool
  proof *.

(* List-consuming oracle (RDO-internal). *)
local module Ref : Iface.Oracle = {
  var xs : out_t list
  proc get() = {
    var r;
    r  <- head witness xs;
    xs <- behead xs;
    return r;
  }
}.

local module B : DistJoint.Dist = {
  proc guess(px : param_t * out_t list) : bool = {
    var r;
    Ref.xs <- px.`2;
    r <@ A(Ref).main(px.`1);
    return r;
  }
}.

(* -- Joint pre-sampled experiments ---------------------------------------
   [G_Joint_i] integrates the [d_param] sample with the per-[p] dlist
   into a single experiment.  Each [Game_i] is provably equivalent to
   the corresponding [G_Joint_i], and the two [G_Joint_i] sides differ
   only in [d_i] (the [d_param] marginal cancels in the pointwise
   ratio), so a single Rényi-∞ application bounds them by [M^N]. *)

local module G_Joint1 = {
  proc main() : bool = {
    var p_val, xs, r;
    p_val      <$ d_param;
    Sampler1.p <- p_val;
    xs         <$ dlist (dtot1 p_val) N;
    BPS1.Ref.xs <- xs;
    r <@ A(BPS1.Ref).main(p_val);
    return r;
  }
}.

local module G_Joint2 = {
  proc main() : bool = {
    var p_val, xs, r;
    p_val      <$ d_param;
    Sampler2.p <- p_val;
    xs         <$ dlist (dtot2 p_val) N;
    BPS2.Ref.xs <- xs;
    r <@ A(BPS2.Ref).main(p_val);
    return r;
  }
}.

(* Transitivity 1: [Game_i] ≡ [G_Joint_i], per event.  Couple the [p]
   draw, then lift the per-[p] fresh≡ref equality through it (bypr + the
   event-generic [BPS_i.eq_pr_fresh_ref_ev]). *)
local lemma Game1_eq_Joint1 (E : bool -> bool) &m :
  Pr[Game1(A).main() @ &m : E res] = Pr[G_Joint1.main() @ &m : E res].
proof.
byequiv => //; proc.
(* Lift each side to a single procedure call to its BPS game. *)
proc change {1} [2..3] : { r <@ BPS1.G(BPS1.Fresh, A).main(p); };
  1: by inline; wp; sim.
proc change {2} [2..5] : { r <@ BPS1.G(BPS1.Ref, A).main(p_val); };
  1: by inline; wp; sim.
(* Couple the [p] sampling. *)
seq 1 1 : (={glob A} /\ p{1} = p_val{2}).
+ rnd; auto.
(* Both sides are now a single procedure call with equal arguments.
   Discharge via [call] + [bypr] using [eq_pr_fresh_ref_ev] per-p. *)
call (_: ={glob A, arg} ==> ={res}).
+ proc*; call (_: ={glob A, arg} ==> ={res}); auto.
  bypr (res{1}) (res{2}) => /> &1 &2 ga gA.
  (* Memory swap: glob A coincides at &1, &2; both procs only read glob A. *)
  have ->: Pr[BPS1.G(BPS1.Fresh, A).main(arg{2}) @ &1 : res = ga]
         = Pr[BPS1.G(BPS1.Fresh, A).main(arg{2}) @ &2 : res = ga].
  + byequiv (_: ={arg, glob A} ==> ={res}) => //; sim.
  exact (BPS1.eq_pr_fresh_ref_ev A A_ll A_bound1 (fun r => r = ga) arg{2} &2).
by auto => />.
qed.

local lemma Game2_eq_Joint2 (E : bool -> bool) &m :
  Pr[Game2(A).main() @ &m : E res] = Pr[G_Joint2.main() @ &m : E res].
proof.
byequiv => //; proc.
proc change {1} [2..3] : { r <@ BPS2.G(BPS2.Fresh, A).main(p); };
  1: by inline; wp; sim.
proc change {2} [2..5] : { r <@ BPS2.G(BPS2.Ref, A).main(p_val); };
  1: by inline; wp; sim.
seq 1 1 : (={glob A} /\ p{1} = p_val{2}).
+ rnd; auto.
call (_: ={glob A, arg} ==> ={res}).
+ proc*; call (_: ={glob A, arg} ==> ={res}); auto.
  bypr (res{1}) (res{2}) => /> &1 &2 ga gA.
  have ->: Pr[BPS2.G(BPS2.Fresh, A).main(arg{2}) @ &1 : res = ga]
         = Pr[BPS2.G(BPS2.Fresh, A).main(arg{2}) @ &2 : res = ga].
  + byequiv (_: ={arg, glob A} ==> ={res}) => //; sim.
  exact (BPS2.eq_pr_fresh_ref_ev A A_ll A_bound2 (fun r => r = ga) arg{2} &2).
by auto => />.
qed.

(* Joint distribution of (p, xs): sample p from d_param, sample xs from
   the per-p dlist, return the pair.  Internal proof plumbing — [local]
   so they do not survive section closure into the public API. *)
local op joint1 = dlet d_param (fun p => dmap (dlist (dtot1 p) N) (fun xs => (p, xs))).
local op joint2 = dlet d_param (fun p => dmap (dlist (dtot2 p) N) (fun xs => (p, xs))).

(* Pointwise simplification: the joint distribution at [(a, ys)]
   collapses to [mu1 d_param a * mu1 (dlist (d_i a) N) ys] because the
   inner [dmap] concentrates on pairs whose first component equals the
   sampled [p]. *)
local lemma joint_pt (di : param_t -> out_t distr) a ys :
  mu1 (dlet d_param (fun p => dmap (dlist (di p) N) (fun xs => (p, xs)))) (a, ys)
  = mu1 d_param a * mu1 (dlist (di a) N) ys.
proof.
rewrite dlet1E (@sumE_fin _ [a]) //=.
- move=> p /=.
  apply contraR => /=; move=> pne_a.
  rewrite dmap1E.
  have -> : ((pred1 (a, ys)) \o (fun xs => (p, xs))) = pred0.
  + by apply/fun_ext => xs; rewrite /pred1 /(\o) /pred0; smt().
  by rewrite mu0.
rewrite big_seq1 /= dmap1E.
congr.
apply mu_eq => xs.
by rewrite /pred1 /(\o) /=; smt().
qed.

(* Bridge: G_Joint_i ≡ Sample(B)(joint_i).  G_Joint_i has Sampler_i.p
   set externally (a "dead store" since A doesn't read Sampler_i.p);
   Sample(B) doesn't.  Both pass [p] as A's argument and supply [xs]
   to the same list-consuming oracle (Ref ≅ BPS_i.Ref by shape). *)
local lemma G_Joint1_vs_Sample (E : bool -> bool) &m :
  Pr[G_Joint1.main() @ &m : E res] = Pr[Sample(B).main(joint1) @ &m : E res].
proof.
byequiv => //; proc; inline B.guess.
swap{1} 2 1.
(* Replace RHS one-step sampling with explicit two-step. *)
proc change {2} [1..2] : [(p_aux : param_t) (xs_aux : out_t list)] {
  p_aux <$ d_param;
  xs_aux <$ dlist (dtot1 p_aux) N;
  px <- (p_aux, xs_aux);
}.
+ wp; rnd : *0 *0; auto.
  move=> &1 _ -> /=; rewrite dmap_id /= !andaE.
  by split=> [? // | [a ys] H_in /=].
seq 2 3 : (={glob A} /\ p_val{1} = px{2}.`1 /\ xs{1} = px{2}.`2).
+ by wp; rnd; rnd; auto.
wp.
call (_: BPS1.Ref.xs{1} = Ref.xs{2}); first by proc; auto.
by auto.
qed.

local lemma G_Joint2_vs_Sample (E : bool -> bool) &m :
  Pr[G_Joint2.main() @ &m : E res] = Pr[Sample(B).main(joint2) @ &m : E res].
proof.
byequiv => //; proc; inline B.guess.
swap{1} 2 1.
proc change {2} [1..2] : [(p_aux : param_t) (xs_aux : out_t list)] {
  p_aux <$ d_param;
  xs_aux <$ dlist (dtot2 p_aux) N;
  px <- (p_aux, xs_aux);
}.
+ wp; rnd : *0 *0; auto.
  move=> &1 _ -> /=; rewrite dmap_id /= !andaE.
  by split=> [? // | [a ys] H_in /=].
seq 2 3 : (={glob A} /\ p_val{1} = px{2}.`1 /\ xs{1} = px{2}.`2).
+ by wp; rnd; rnd; auto.
wp.
call (_: BPS2.Ref.xs{1} = Ref.xs{2}); first by proc; auto.
by auto.
qed.

(* Pointwise [M^N] uniform bound of joint1 by joint2: for p ∉ supp d_param
   the dlet integrand vanishes; for p ∈ supp d_param we use
   [d1_dominated_d2] composed with dlist tensorization. *)
local lemma joint_pt_bound (a : param_t) ys :
  mu1 joint1 (a, ys) <= M ^ N * mu1 joint2 (a, ys).
proof.
rewrite /joint1 /joint2 !joint_pt.
case (a \in d_param) => a_in.
+ rewrite (dtot1E a a_in) (dtot2E a a_in).
  have dom_a : dominated M (d1 a) (d2 a)
    by split; [exact M_ge0 | exact (d1_dominated_d2 a a_in)].
  have [_ dlist_all] := dominated_dlist M (d1 a) (d2 a) N N_ge0 dom_a.
  have dlist_pt := dlist_all ys.
  have ge0_mup : 0%r <= mu1 d_param a by exact ge0_mu1.
  smt(ge0_mu1).
+ have -> : mu1 d_param a = 0%r by smt(supportP).
  by rewrite mul0r mulr0; smt(M_ge0 expr_ge0 N_ge0).
qed.

local lemma joint_dom : dominated (M ^ N) joint1 joint2.
proof.
split; first by smt(M_ge0 expr_ge0 N_ge0).
by case=> a ys; exact (joint_pt_bound a ys).
qed.

local lemma joint_rdiv_inf_bound : rdiv_inf joint1 joint2 <= M ^ N.
proof. exact (rdiv_inf_le _ _ _ joint_dom). qed.

(* Transitivity 2 (the Rényi step): single application of [adv_rdiv_inf_le]
   on the joint distribution. *)
local lemma Joint_rdiv_bound (E : bool -> bool) &m :
  Pr[G_Joint1.main() @ &m : E res] <=
    M ^ N *
    Pr[G_Joint2.main() @ &m : E res].
proof.
rewrite (G_Joint1_vs_Sample E &m) (G_Joint2_vs_Sample E &m).
apply (adv_rdiv_inf_le B E &m (M ^ N)).
- exact joint_dom.
- exact joint_rdiv_inf_bound.
qed.

(* -- PUBLIC: parametric user-facing lemma, per event ---------------------- *)

lemma rdiv_bound_sampler (E : bool -> bool) &m :
  Pr[Game1(A).main() @ &m : E res] <=
    M ^ N *
    Pr[Game2(A).main() @ &m : E res].
proof.
rewrite (Game1_eq_Joint1 E &m) (Game2_eq_Joint2 E &m).
exact (Joint_rdiv_bound E &m).
qed.

end section.

end RDivOracle.

(* ==========================================================================

   Restricted layer: the valid-parameter surface over the REAL experiment.

   Some developments only have the per-parameter hypotheses (losslessness,
   dominance) on a subset of "good" parameters — e.g. MAYO's rejection-
   sampling guarantee holds except for a negligible set of bad keys.  In
   [RDivOracle] that restriction is an instantiation: condition [d_param].
   This theory packages that instantiation for the common shape where the
   consumer's games sample from the FULL distribution [d_full] (the real
   key-generation) and excise bad parameters at the event level:

     [rdiv_bound_sampler] :
       Pr[GameV1(A) : E res /\ valid Sampler1.p]
         <= M ^ N * Pr[GameV2(A) : E res /\ valid Sampler2.p]

   — validity as an event conjunct over the game-stored parameter, with NO
   additive slack and NO [M >= 1] assumption: bad parameters behave
   identically in both games, and the validity conjunct removes their mass
   from both sides.  The corollary [rdiv_bound_sampler_le] trades the
   conjunct for the additive bad-parameter mass:

     Pr[GameV1(A) : E res]
       <= M ^ N * Pr[GameV2(A) : E res] + mu d_full (predC valid).

   (An [M >= 1]-free bound for arbitrary events without the additive term
   is impossible: events that count bad-parameter runs weigh their equal
   mass on both sides, which only [M ^ N >= 1] could absorb.)

   Internally: clone [RDivOracle] at [d_param <- dcond d_full valid]
   ([Core]) and prove the conditioning hop once per side ([cond_factor1],
   mirrored as [cond_factor2]),

     Pr[GameV1(A) : E res /\ valid p]
       = mu d_full valid * Pr[Core.Game1(A) : E res]

   by reflecting both game families into [Distinguisher.Sample] over a
   distinguisher returning [(p, r)] pairs ([GameV1_Sample],
   [CoreGame1_Sample]), where the hop is plain distribution theory:
   [Sample1_dcond_valid] makes the validity conjunct free on the
   conditioned source, and [Sample1_cond_factor] factors out
   [mu d_full valid] ([dletE] + [dcond1E]).  The public
   [rdiv_bound_sampler] chains [cond_factor1], [Core.rdiv_bound_sampler]
   and [cond_factor2]; [rdiv_bound_sampler_le] adds [GameV1_invalid_le]
   for the bad-parameter mass.

   The consumer's own bad-key payment (e.g. MAYO's [eps_key] hop from
   "wins" to "wins on valid keys") stays on the consumer side, where the
   key-generation procedure lives.

   ========================================================================== *)

abstract theory RDivOracleValid.

type out_t.
type param_t.

(* Same sharing story as [RDivOracle.Iface] — see the note there. *)
clone import BPS_Iface as Iface with
  type out_t   <= out_t,
  type param_t <= param_t.

op [lossless] d_full : param_t distr.
op valid : param_t -> bool.

op d1 : param_t -> out_t distr.
op d2 : param_t -> out_t distr.

axiom d1_ll : forall p, p \in d_full => valid p => is_lossless (d1 p).
axiom d2_ll : forall p, p \in d_full => valid p => is_lossless (d2 p).

op N : { int | 0 <= N } as N_ge0.
op M : { real | 0%r <= M } as M_ge0.

axiom d1_dominated_d2 :
  forall p, p \in d_full => valid p =>
    forall x, mu1 (d1 p) x <= M * mu1 (d2 p) x.

(* Good parameters have positive mass (in MAYO: >= 1 - eps_key > 0). *)
axiom valid_nondegenerate : 0%r < mu d_full valid.

clone RDivOracle as Core with
  type out_t   <- out_t,
  type param_t <- param_t,
  theory Iface <- Iface,
  op d_param   <- dcond d_full valid,
  op d1        <- d1,
  op d2        <- d2,
  op N         <- N,
  op M         <- M
  proof *.
realize d_param_ll by apply dcond_ll; exact valid_nondegenerate.
realize d1_ll by move => p /dcond_supp [p_in v_p]; exact (d1_ll p p_in v_p).
realize d2_ll by move => p /dcond_supp [p_in v_p]; exact (d2_ll p p_in v_p).
realize N_ge0 by exact N_ge0.
realize M_ge0 by exact M_ge0.
realize d1_dominated_d2
  by move => p /dcond_supp [p_in v_p]; exact (d1_dominated_d2 p p_in v_p).

(* Public sampler names (aliases of the Core samplers). *)
module Sampler1 = Core.Sampler1.
module Sampler2 = Core.Sampler2.

(* Consumer-facing kernel identities: on valid parameters of [d_full],
   the samplers draw exactly [d_i p].  Cite these instead of unfolding
   the internal totalized kernels ([Core.dtot_i]). *)
lemma Sampler1_dE p : p \in d_full => valid p => Core.dtot1 p = d1 p.
proof. by move => p_in v_p; apply Core.dtot1E; rewrite dcond_supp. qed.

lemma Sampler2_dE p : p \in d_full => valid p => Core.dtot2 p = d2 p.
proof. by move => p_in v_p; apply Core.dtot2E; rewrite dcond_supp. qed.

(* The REAL experiments: parameter drawn from the full distribution. *)
module GameV1 (A : Adv) = {
  proc main() : bool = {
    var p, r;
    p <$ d_full;
    Sampler1.p <- p;
    r <@ A(Sampler1).main(p);
    return r;
  }
}.

module GameV2 (A : Adv) = {
  proc main() : bool = {
    var p, r;
    p <$ d_full;
    Sampler2.p <- p;
    r <@ A(Sampler2).main(p);
    return r;
  }
}.

(* -- Section: the conditioning hop and the public bounds ------------------
   MIRRORING: as in [RDivOracle], side-2 items are verbatim mirrors of
   their side-1 twins (1 -> 2 in every name); audit side 1, diff side 2. *)

section.

declare module A <: Adv
  { -Core.Sampler1, -Core.Sampler2, -Core.BPS1.Count, -Core.BPS2.Count,
    -Core.BPS1.Ref, -Core.BPS2.Ref }.

declare axiom A_ll :
  forall (O <: Oracle { -A }),
    islossless O.get => islossless A(O).main.

declare axiom A_bound1 :
  hoare[ A(Core.BPS1.Count(Core.Sampler1)).main :
    Core.BPS1.Count.n = 0 ==> Core.BPS1.Count.n <= N ].

declare axiom A_bound2 :
  hoare[ A(Core.BPS2.Count(Core.Sampler2)).main :
    Core.BPS2.Count.n = 0 ==> Core.BPS2.Count.n <= N ].

(* Distinguisher clone for the conditioning hop: inputs are parameters,
   outputs are [(p, r)] pairs so events can inspect the drawn parameter. *)
local clone import Distinguisher as DistP with
  type in_t  <- param_t,
  type out_t <- param_t * bool
  proof *.

local module BP1 : DistP.Dist = {
  proc guess(p : param_t) : param_t * bool = {
    var r;
    Core.Sampler1.p <- p;
    r <@ A(Core.Sampler1).main(p);
    return (p, r);
  }
}.

local module BP2 : DistP.Dist = {
  proc guess(p : param_t) : param_t * bool = {
    var r;
    Core.Sampler2.p <- p;
    r <@ A(Core.Sampler2).main(p);
    return (p, r);
  }
}.

(* Shape lemmas: both game families are [Sample] in disguise. *)
local lemma GameV1_Sample (F : bool -> param_t -> bool) &m :
  Pr[GameV1(A).main() @ &m : F res Core.Sampler1.p]
  = Pr[Sample(BP1).main(d_full) @ &m : F res.`2 res.`1].
proof.
byequiv (: ={glob A, glob Core.Sampler1} /\ arg{2} = d_full
           ==> res{2} = (Core.Sampler1.p{1}, res{1})) => //.
proc; inline BP1.guess; wp.
call (: ={glob Core.Sampler1}); first by proc; auto.
by auto.
qed.

local lemma GameV2_Sample (F : bool -> param_t -> bool) &m :
  Pr[GameV2(A).main() @ &m : F res Core.Sampler2.p]
  = Pr[Sample(BP2).main(d_full) @ &m : F res.`2 res.`1].
proof.
byequiv (: ={glob A, glob Core.Sampler2} /\ arg{2} = d_full
           ==> res{2} = (Core.Sampler2.p{1}, res{1})) => //.
proc; inline BP2.guess; wp.
call (: ={glob Core.Sampler2}); first by proc; auto.
by auto.
qed.

local lemma CoreGame1_Sample (E : bool -> bool) &m :
  Pr[Core.Game1(A).main() @ &m : E res]
  = Pr[Sample(BP1).main(dcond d_full valid) @ &m : E res.`2].
proof.
byequiv (: ={glob A, glob Core.Sampler1} /\ arg{2} = dcond d_full valid
           ==> res{1} = res{2}.`2) => //.
proc; inline BP1.guess; wp.
call (: ={glob Core.Sampler1}); first by proc; auto.
by auto.
qed.

local lemma CoreGame2_Sample (E : bool -> bool) &m :
  Pr[Core.Game2(A).main() @ &m : E res]
  = Pr[Sample(BP2).main(dcond d_full valid) @ &m : E res.`2].
proof.
byequiv (: ={glob A, glob Core.Sampler2} /\ arg{2} = dcond d_full valid
           ==> res{1} = res{2}.`2) => //.
proc; inline BP2.guess; wp.
call (: ={glob Core.Sampler2}); first by proc; auto.
by auto.
qed.

(* Concentration: [BP_i.guess(x)] always returns a pair with first
   component [x]. *)
local lemma BP1_fst &m (x0 : param_t) (z : param_t * bool) :
  z.`1 <> x0 => Pr[BP1.guess(x0) @ &m : res = z] = 0%r.
proof.
move => neq; byphoare (: arg = x0 ==> res = z) => //.
hoare; proc; wp; call (: true); auto => /> /#.
qed.

local lemma BP2_fst &m (x0 : param_t) (z : param_t * bool) :
  z.`1 <> x0 => Pr[BP2.guess(x0) @ &m : res = z] = 0%r.
proof.
move => neq; byphoare (: arg = x0 ==> res = z) => //.
hoare; proc; wp; call (: true); auto => /> /#.
qed.

(* Support form of concentration, phrased on the [mk] kernels that
   [Sample_dletE] introduces. *)
local lemma BP1_supp_fst &m (x : param_t) (z : param_t * bool) :
  z \in mk (fun z0 => Pr[BP1.guess(x) @ &m : res = z0]) => z.`1 = x.
proof.
case (z.`1 = x) => // neq z_in.
move: z_in; rewrite supportP -(GD.adv_mu1 BP1 &m z x).
by rewrite (BP1_fst &m x z neq).
qed.

local lemma BP2_supp_fst &m (x : param_t) (z : param_t * bool) :
  z \in mk (fun z0 => Pr[BP2.guess(x) @ &m : res = z0]) => z.`1 = x.
proof.
case (z.`1 = x) => // neq z_in.
move: z_in; rewrite supportP -(GD.adv_mu1 BP2 &m z x).
by rewrite (BP2_fst &m x z neq).
qed.

(* On the conditioned source, every reachable pair carries a valid
   parameter — the validity conjunct is free. *)
local lemma Sample1_dcond_valid (E : bool -> bool) &m :
  Pr[Sample(BP1).main(dcond d_full valid) @ &m : E res.`2]
  = Pr[Sample(BP1).main(dcond d_full valid) @ &m : E res.`2 /\ valid res.`1].
proof.
rewrite (Sample_dletE BP1 (fun (z : param_t * bool) => E z.`2) &m).
rewrite (Sample_dletE BP1 (fun (z : param_t * bool) => E z.`2 /\ valid z.`1) &m).
apply mu_eq_support => z /supp_dlet [x [x_in z_in]] /=.
have z1 : z.`1 = x by exact (BP1_supp_fst &m x z z_in).
by move: x_in => /dcond_supp [_ v_x]; rewrite z1 v_x.
qed.

local lemma Sample2_dcond_valid (E : bool -> bool) &m :
  Pr[Sample(BP2).main(dcond d_full valid) @ &m : E res.`2]
  = Pr[Sample(BP2).main(dcond d_full valid) @ &m : E res.`2 /\ valid res.`1].
proof.
rewrite (Sample_dletE BP2 (fun (z : param_t * bool) => E z.`2) &m).
rewrite (Sample_dletE BP2 (fun (z : param_t * bool) => E z.`2 /\ valid z.`1) &m).
apply mu_eq_support => z /supp_dlet [x [x_in z_in]] /=.
have z1 : z.`1 = x by exact (BP2_supp_fst &m x z z_in).
by move: x_in => /dcond_supp [_ v_x]; rewrite z1 v_x.
qed.

(* The conditioning hop at the distribution level: for validity-entailing
   events, sampling from [d_full] equals [mu d_full valid] times sampling
   from the conditioned distribution. *)
local lemma Sample1_cond_factor (G : param_t * bool -> bool) &m :
  (forall z, G z => valid z.`1) =>
  Pr[Sample(BP1).main(d_full) @ &m : G res]
  = mu d_full valid * Pr[Sample(BP1).main(dcond d_full valid) @ &m : G res].
proof.
move => G_valid.
rewrite (Sample_dletE BP1 G &m d_full).
rewrite (Sample_dletE BP1 G &m (dcond d_full valid)).
have T0 : forall x, !valid x =>
  mu (mk (fun z0 => Pr[BP1.guess(x) @ &m : res = z0])) G = 0%r.
+ move => x nv.
  rewrite (mu_eq_support _ G pred0) 2:mu0 // => z /(BP1_supp_fst &m x) z1.
  by rewrite /pred0 /=; smt().
rewrite !dletE -sumZ.
apply eq_sum => x /=.
rewrite dcond1E.
case (valid x) => v_x; last first.
+ by rewrite (T0 x v_x) !mulr0.
have nz : mu d_full valid <> 0%r by smt(valid_nondegenerate).
by field.
qed.

local lemma Sample2_cond_factor (G : param_t * bool -> bool) &m :
  (forall z, G z => valid z.`1) =>
  Pr[Sample(BP2).main(d_full) @ &m : G res]
  = mu d_full valid * Pr[Sample(BP2).main(dcond d_full valid) @ &m : G res].
proof.
move => G_valid.
rewrite (Sample_dletE BP2 G &m d_full).
rewrite (Sample_dletE BP2 G &m (dcond d_full valid)).
have T0 : forall x, !valid x =>
  mu (mk (fun z0 => Pr[BP2.guess(x) @ &m : res = z0])) G = 0%r.
+ move => x nv.
  rewrite (mu_eq_support _ G pred0) 2:mu0 // => z /(BP2_supp_fst &m x) z1.
  by rewrite /pred0 /=; smt().
rewrite !dletE -sumZ.
apply eq_sum => x /=.
rewrite dcond1E.
case (valid x) => v_x; last first.
+ by rewrite (T0 x v_x) !mulr0.
have nz : mu d_full valid <> 0%r by smt(valid_nondegenerate).
by field.
qed.

(* The conditioning hop, per side. *)
local lemma cond_factor1 (E : bool -> bool) &m :
  Pr[GameV1(A).main() @ &m : E res /\ valid Core.Sampler1.p]
  = mu d_full valid * Pr[Core.Game1(A).main() @ &m : E res].
proof.
rewrite (GameV1_Sample (fun r p => E r /\ valid p) &m) /=.
rewrite (CoreGame1_Sample E &m) (Sample1_dcond_valid E &m).
apply (Sample1_cond_factor (fun (z : param_t * bool) => E z.`2 /\ valid z.`1) &m).
by move => z [].
qed.

local lemma cond_factor2 (E : bool -> bool) &m :
  Pr[GameV2(A).main() @ &m : E res /\ valid Core.Sampler2.p]
  = mu d_full valid * Pr[Core.Game2(A).main() @ &m : E res].
proof.
rewrite (GameV2_Sample (fun r p => E r /\ valid p) &m) /=.
rewrite (CoreGame2_Sample E &m) (Sample2_dcond_valid E &m).
apply (Sample2_cond_factor (fun (z : param_t * bool) => E z.`2 /\ valid z.`1) &m).
by move => z [].
qed.

(* -- PUBLIC: the restricted bound, per validity-entailing event ----------- *)

lemma rdiv_bound_sampler (E : bool -> bool) &m :
  Pr[GameV1(A).main() @ &m : E res /\ valid Core.Sampler1.p] <=
    M ^ N *
    Pr[GameV2(A).main() @ &m : E res /\ valid Core.Sampler2.p].
proof.
rewrite (cond_factor1 E &m) (cond_factor2 E &m) mulrCA.
apply ler_wpmul2l; first by smt(valid_nondegenerate).
exact (Core.rdiv_bound_sampler A A_ll A_bound1 A_bound2 E &m).
qed.

(* Bad-parameter mass at the game level. *)
local lemma GameV1_invalid_le &m :
  Pr[GameV1(A).main() @ &m : !valid Core.Sampler1.p]
  <= mu d_full (predC valid).
proof.
rewrite (GameV1_Sample (fun _ p => !valid p) &m) /=.
rewrite (Sample_dletE BP1 (fun (z : param_t * bool) => !valid z.`1) &m).
rewrite dletE muE.
apply ler_sum.
+ move => x /=.
  case (valid x) => v_x.
  - have -> : mu (mk (fun z0 => Pr[BP1.guess(x) @ &m : res = z0]))
                 (fun (z : param_t * bool) => !valid z.`1) = 0%r.
    * rewrite (mu_eq_support _ _ pred0) 2:mu0 //.
      by move => z /(BP1_supp_fst &m x) z1; rewrite /pred0 /= z1 v_x.
    by rewrite mulr0 /=.
  - rewrite /=.
    apply (ler_trans (mu1 d_full x * 1%r)); 2: by rewrite mulr1.
    by apply ler_wpmul2l; [exact ge0_mu1 | exact le1_mu].
+ by apply summable_mu1_wght => x; smt(ge0_mu le1_mu).
+ apply (summable_le (mu1 d_full)); first exact summable_mu1.
  by move => x /=; smt(ge0_mu1).
qed.

(* Corollary: trade the validity conjunct for the additive bad-parameter
   mass.  No [M >= 1] needed: the conjunct form absorbs on the good side
   and the bad side is bounded outright. *)
lemma rdiv_bound_sampler_le (E : bool -> bool) &m :
  Pr[GameV1(A).main() @ &m : E res] <=
    M ^ N * Pr[GameV2(A).main() @ &m : E res]
    + mu d_full (predC valid).
proof.
rewrite Pr[mu_split (valid Core.Sampler1.p)].
apply (ler_trans (M ^ N * Pr[GameV2(A).main() @ &m : E res /\ valid Core.Sampler2.p]
                  + mu d_full (predC valid))).
+ apply ler_add; first exact (rdiv_bound_sampler E &m).
  apply (ler_trans (Pr[GameV1(A).main() @ &m : !valid Core.Sampler1.p]));
    first by rewrite Pr[mu_sub] // /#.
  exact (GameV1_invalid_le &m).
rewrite ler_add2r.
apply ler_wpmul2l; first by smt(M_ge0 expr_ge0 N_ge0).
by rewrite Pr[mu_sub].
qed.

end section.

end RDivOracleValid.
