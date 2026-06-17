(* ==========================================================================

   Rényi-∞ oracle bound for bounded-query sequential adversaries,
   PARAMETRIC over a shared secret parameter [p : param_t].

   User-facing lemma [rdiv_bound_sampler] concludes, for an A with bounded
   query count N against fresh i.i.d. samplers:

     Pr[Game1(A).main @ &m : res] <= M ^ N * Pr[Game2(A).main @ &m : res]

   where:
   - [Game_i] samples [p <$ d_param], sets [Sampler_i.p := p], then runs A.
   - [Sampler1.get] returns a fresh draw from [d1 p].
   - [Sampler2.get] returns a fresh draw from [d2 p].
   - [M] is an explicit uniform dominance witness:
       forall p ∈ supp d_param, forall x, mu1 (d1 p) x ≤ M * mu1 (d2 p) x.
   - [N] is A's query budget.

   Non-parametric specialization:
     [param_t := unit, d_param := dunit (), d1 := fun _ => d, d2 := fun _ => d'].

   ARCHITECTURE: presampling is fully delegated to [BoundedPreSample.ec].
   BPS1, BPS2 (clones for d1, d2) provide the [pr_fresh_eq_presampled]
   Pr-equality between fresh-sampling and pre-sampled-list games.  Two
   clones share [Iface] (Oracle/Adv module types) so a single [A] applies.

   The internal per-p chain is just two hops:

       BPS_i.G_Fresh(A).main(p)
          ≡ (via BPS_i.pr_fresh_eq_presampled, requires A_bound_i)
       BPS_i.G_PreSampled(A).main(p)
          ≡ (trivial byequiv, shape rename)
       DL.Sample(B).main(dlist (d_i p) N)

   Then [adv_rdiv_inf_dlist] gives M^N · Sample(B) on d2.

   ========================================================================== *)

require import AllCore List Distr DList StdOrder StdRing StdBigop FMap RealSeries.
require import RDiv.
require import FinType.
require import BoundedPreSample.
(*---*) import RField RealOrder Bigreal.BRA.

abstract theory RDivOracle.

(* -- Parameters ----------------------------------------------------------- *)

type out_t.
type param_t.

clone FinType as ParamFin with type t <- param_t.

(* Single Iface clone — both top-level access target (consumers use
   [RDO.Iface.Oracle]/[RDO.Iface.Adv]) and BPS substitution target. *)
clone import BPS_Iface as Iface with
  type out_t   = out_t,
  type param_t = param_t.

op [lossless] d_param : param_t distr.

op d1 : param_t -> out_t distr.
op d2 : param_t -> out_t distr.

axiom d1_ll : forall p, is_lossless (d1 p).
axiom d2_ll : forall p, is_lossless (d2 p).

op N : { int | 0 <= N } as N_ge0.
op M : { real | 0%r <= M } as M_ge0.

axiom dominated_12_uniform :
  forall p, p \in d_param =>
    forall x, mu1 (d1 p) x <= M * mu1 (d2 p) x.

(* -- BoundedPreSample clones ---------------------------------------------- *)

clone BoundedPreSample as BPS1 with
  type out_t       = out_t,
  type param_t     = param_t,
  theory Iface     <- Iface,
  op    d          <- d1,
  op    d_param    <- d_param,
  op    N          <- N
  proof *.
realize d_ll       by exact d1_ll.
realize N_ge0      by exact N_ge0.
realize d_param_ll by exact d_param_ll.

clone BoundedPreSample as BPS2 with
  type out_t       = out_t,
  type param_t     = param_t,
  theory Iface     <- Iface,
  op    d          <- d2,
  op    d_param    <- d_param,
  op    N          <- N
  proof *.
realize d_ll       by exact d2_ll.
realize N_ge0      by exact N_ge0.
realize d_param_ll by exact d_param_ll.

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

(* -- Section: A, axioms, internal Rényi chain, user-facing lemma ---------- *)

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
    xs         <$ dlist (d1 p_val) N;
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
    xs         <$ dlist (d2 p_val) N;
    BPS2.Ref.xs <- xs;
    r <@ A(BPS2.Ref).main(p_val);
    return r;
  }
}.

(* Fresh ≡ Ref at the Pr level on any [res] event.  BPS exposes
   [eq_pr_fresh_ref] for the event [res]; this lifts it to [res = E] using
   losslessness of both games — the one delicate step, isolated here so the
   transitivity bridges below read cleanly. *)
local lemma pr1_fresh_ref_ev (p : param_t) (E : bool) &n :
  Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : res = E]
  = Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : res = E].
proof.
have BPSeq := BPS1.eq_pr_fresh_ref A A_ll A_bound1 p &n.
have F_ll : Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : true] = 1%r.
+ byphoare => //; proc; call (A_ll BPS1.Fresh _); 1: by proc; auto; smt(d1_ll).
  by inline*; auto.
have P_ll : Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : true] = 1%r.
+ byphoare => //; proc; call (A_ll BPS1.Ref _); 1: by proc; auto.
  by inline*; auto; smt(dlist_ll d1_ll N_ge0).
case E => _.
+ have ->: Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : res = true]
         = Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : res] by rewrite Pr[mu_eq] // /#.
  have ->: Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : res = true]
         = Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : res] by rewrite Pr[mu_eq] // /#.
  exact BPSeq.
have ->: Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : res = false]
       = Pr[BPS1.G(BPS1.Fresh, A).main(p) @ &n : !res] by rewrite Pr[mu_eq] // /#.
have ->: Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : res = false]
       = Pr[BPS1.G(BPS1.Ref, A).main(p) @ &n : !res] by rewrite Pr[mu_eq] // /#.
by rewrite Pr[mu_not] Pr[mu_not] F_ll P_ll BPSeq.
qed.

local lemma pr2_fresh_ref_ev (p : param_t) (E : bool) &n :
  Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : res = E]
  = Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : res = E].
proof.
have BPSeq := BPS2.eq_pr_fresh_ref A A_ll A_bound2 p &n.
have F_ll : Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : true] = 1%r.
+ byphoare => //; proc; call (A_ll BPS2.Fresh _); 1: by proc; auto; smt(d2_ll).
  by inline*; auto.
have P_ll : Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : true] = 1%r.
+ byphoare => //; proc; call (A_ll BPS2.Ref _); 1: by proc; auto.
  by inline*; auto; smt(dlist_ll d2_ll N_ge0).
case E => _.
+ have ->: Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : res = true]
         = Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : res] by rewrite Pr[mu_eq] // /#.
  have ->: Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : res = true]
         = Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : res] by rewrite Pr[mu_eq] // /#.
  exact BPSeq.
have ->: Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : res = false]
       = Pr[BPS2.G(BPS2.Fresh, A).main(p) @ &n : !res] by rewrite Pr[mu_eq] // /#.
have ->: Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : res = false]
       = Pr[BPS2.G(BPS2.Ref, A).main(p) @ &n : !res] by rewrite Pr[mu_eq] // /#.
by rewrite Pr[mu_not] Pr[mu_not] F_ll P_ll BPSeq.
qed.

(* Transitivity 1: [Game_i] ≡ [G_Joint_i].  Couple the [p] draw, then lift the
   per-[p] fresh≡ref equality through it (bypr + the [prX_fresh_ref_ev] helper). *)
local lemma Game1_eq_Joint1 &m :
  Pr[Game1(A).main() @ &m : res] = Pr[G_Joint1.main() @ &m : res].
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
   Discharge via [call] + [bypr] using [eq_pr_fresh_ref] per-p. *)
call (_: ={glob A, arg} ==> ={res}).
+ proc*; call (_: ={glob A, arg} ==> ={res}); auto.
  bypr (res{1}) (res{2}) => /> &1 &2 ga gA.
  (* Memory swap: glob A coincides at &1, &2; both procs only read glob A. *)
  have ->: Pr[BPS1.G(BPS1.Fresh, A).main(arg{2}) @ &1 : res = ga]
         = Pr[BPS1.G(BPS1.Fresh, A).main(arg{2}) @ &2 : res = ga].
  + byequiv (_: ={arg, glob A} ==> ={res}) => //; sim.
  exact (pr1_fresh_ref_ev arg{2} ga &2).
auto.
qed.

local lemma Game2_eq_Joint2 &m :
  Pr[Game2(A).main() @ &m : res] = Pr[G_Joint2.main() @ &m : res].
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
  exact (pr2_fresh_ref_ev arg{2} ga &2).
auto.
qed.

(* Joint distribution of (p, xs): sample p from d_param, sample xs from
   the per-p dlist, return the pair. *)
op joint1 = dlet d_param (fun p => dmap (dlist (d1 p) N) (fun xs => (p, xs))).
op joint2 = dlet d_param (fun p => dmap (dlist (d2 p) N) (fun xs => (p, xs))).

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
local lemma G_Joint1_vs_Sample &m :
  Pr[G_Joint1.main() @ &m : res] = Pr[Sample(B).main(joint1) @ &m : res].
proof.
byequiv => //; proc; inline B.guess.
swap{1} 2 1.
(* Replace RHS one-step sampling with explicit two-step. *)
proc change {2} [1..2] : [(p_aux : param_t) (xs_aux : out_t list)] {
  p_aux <$ d_param;
  xs_aux <$ dlist (d1 p_aux) N;
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

local lemma G_Joint2_vs_Sample &m :
  Pr[G_Joint2.main() @ &m : res] = Pr[Sample(B).main(joint2) @ &m : res].
proof.
byequiv => //; proc; inline B.guess.
swap{1} 2 1.
proc change {2} [1..2] : [(p_aux : param_t) (xs_aux : out_t list)] {
  p_aux <$ d_param;
  xs_aux <$ dlist (d2 p_aux) N;
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
   [dominated_12_uniform] composed with dlist tensorization. *)
local lemma joint_pt_bound (a : param_t) ys :
  mu1 joint1 (a, ys) <= M ^ N * mu1 joint2 (a, ys).
proof.
rewrite /joint1 /joint2 !joint_pt.
case (a \in d_param) => a_in.
+ have dom_a : dominated M (d1 a) (d2 a)
    by split; [exact M_ge0 | exact (dominated_12_uniform a a_in)].
  have rinf_dlist : rdiv_inf (dlist (d1 a) N) (dlist (d2 a) N) <= M ^ N.
  + apply (ler_trans (RField.exp (rdiv_inf (d1 a) (d2 a)) N));
      first exact (rdiv_inf_dlist _ _ _ _ N_ge0 dom_a).
    apply ler_pexp; first by smt(N_ge0).
    split; first exact (rdiv_inf_ge0 _ _ _ dom_a).
    by move=> _; apply rdiv_inf_le_ub;
       [exact M_ge0 | exact (dominated_12_uniform a a_in)].
  have dlist_pt : mu1 (dlist (d1 a) N) ys <= M ^ N * mu1 (dlist (d2 a) N) ys.
  + apply (ler_trans (rdiv_inf (dlist (d1 a) N) (dlist (d2 a) N) * mu1 (dlist (d2 a) N) ys)).
    + exact (rdiv_inf_upper_bound _ _ _ _ (dominated_dlist _ _ _ _ N_ge0 dom_a)).
    by apply ler_wpmul2r; [exact ge0_mu1 | exact rinf_dlist].
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
proof.
apply rdiv_inf_le_ub; first by smt(M_ge0 expr_ge0 N_ge0).
by case=> a ys; exact (joint_pt_bound a ys).
qed.

(* Transitivity 2 (the Rényi step): single application of [adv_rdiv_inf]
   on the joint distribution. *)
local lemma Joint_rdiv_bound &m :
  Pr[G_Joint1.main() @ &m : res] <=
    M ^ N *
    Pr[G_Joint2.main() @ &m : res].
proof.
rewrite (G_Joint1_vs_Sample &m) (G_Joint2_vs_Sample &m).
apply (ler_trans _ _ _ (adv_rdiv_inf B (fun b => b) &m (M ^ N) joint1 joint2 joint_dom)).
apply ler_wpmul2r; first by rewrite Pr[mu_ge0].
exact joint_rdiv_inf_bound.
qed.

(* -- PUBLIC: parametric user-facing lemma -------------------------------- *)

lemma rdiv_bound_sampler &m :
  Pr[Game1(A).main() @ &m : res] <=
    M ^ N *
    Pr[Game2(A).main() @ &m : res].
proof.
rewrite (Game1_eq_Joint1 &m) (Game2_eq_Joint2 &m).
exact (Joint_rdiv_bound &m).
qed.

end section.

end RDivOracle.
