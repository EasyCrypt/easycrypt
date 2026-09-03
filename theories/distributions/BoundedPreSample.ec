(* ==========================================================================

   BoundedPreSample: presampling library for bounded-query sequential
   adversaries, parametric over a shared parameter [p : param_t].  The
   parameter is NOT hidden from the adversary: the games hand [p] to
   [A.main] in the clear (the exported equality holds a fortiori for
   parameter-aware adversaries).

   Exports one probability equality per event, [eq_pr_fresh_ref_ev]
   (with [eq_pr_fresh_ref] the [res] specialization):

     Pr[G(Fresh, A).main(p) : E res] = Pr[G(Ref, A).main(p) : E res]

   between A run against a bare fresh sampler ([Fresh] draws from [d p] on
   every query) and A run against a pre-sampled list of N draws ([Ref] pops
   successive elements of a [dlist (d p) N]).

   Hypotheses (section context): [A_bound] — A makes at most N queries —
   and [A_ll] — A is lossless whenever its oracle is.  Losslessness is not
   an afterthought: the internal bridge is an upto-bad step relating
   [Fresh] to the [BCount]-guarded sampler, whose bad event ("A asked for
   query N+1") has probability 0 precisely because A is N-bounded; the
   guarded sampler then ticks in lockstep with list exhaustion, and eager
   sampling (via [PROM.FullRO]'s [FullEager.RO_LRO_D]) converts the
   guarded fresh draws into the pre-sampled list.

   Module-type sharing: [Oracle] and [Adv] are declared in a nested
   sub-theory [Iface], which is cloned into the main theory.  Consumers
   that clone [BoundedPreSample] multiple times (e.g., for different
   distributions [d1], [d2]) can share a single external [Iface] clone
   across all uses via [theory I <- ...] substitution, preserving the
   nominal identity of [Oracle]/[Adv] across the clones.

   Typical use: clone this theory, instantiate d/N, compose the public
   [eq_pr_fresh_ref_ev] lemma with downstream reasoning on the
   pre-sampled list (e.g., RDiv.DistinguisherList for Rényi-∞, or direct
   coupling arguments).

   ========================================================================== *)

require import AllCore List Distr DList FMap.

require (*..*) PROM.

(* ---- Shared interface: Oracle and Adv module types ---------------------- *)

abstract theory BPS_Iface.

type out_t, param_t.

module type Sampler = {
  proc init(_: param_t): unit
  proc get(): out_t
}.

module type Oracle = {
  include Sampler [get]
}.

module type Adv (O : Oracle) = {
  proc main(p : param_t) : bool
}.

end BPS_Iface.
(* NOTE: Iface must contain ONLY types and module types — no concrete
   modules (EC clone substitution rejects theories containing modules).
   Count lives in the main BoundedPreSample theory. *)

(* ---- Main theory -------------------------------------------------------- *)

abstract theory BoundedPreSample.

type out_t, param_t.

(* -- Parameters ----------------------------------------------------------- *)

op d: param_t -> out_t distr.
axiom d_ll p: is_lossless (d p).

op N : { int | 0 <= N } as N_ge0.

clone import BPS_Iface as Iface with
  type out_t   <= out_t,
  type param_t <= param_t.
(* Iface sub-theory created; Oracle/Adv in scope via import. *)

(* Query counter — Count lives outside Iface (EC clone subst limitation).
   Per-clone Count.n; consumers state A_bound against their specific
   clone's Count (e.g. BPS1.Count for the d1 side). *)
module Count (S : Sampler) = {
  var n : int

  proc init(p: param_t) = {
    S.init(p);
    n <- 0;
  }

  proc get() = {
    var r;
    n <- n + 1;
    r <@ S.get();
    return r;
  }
}.

(* -- Public modules ------------------------------------------------------- *)

(* Fresh sampler (parameter-aware).  The parameter [p] is set by the
   enclosing game (e.g., [G.main]) before A is invoked. *)
module Fresh : Sampler = {
  var p : param_t

  proc init(p') = {
    p <- p';
  }

  proc get() = {
    var r;

    r <$ d p;
    return r;
  }
}.

(* Pre-sampled list consumer.  After N pops the list is empty; subsequent
   calls return [head witness [] = witness] — same witness-after-exhaust
   behavior as BCount. *)
module Ref : Oracle = {
  var xs : out_t list

  proc init(p) = {
    xs <$ dlist (d p) N;
  }

  proc get() = {
    var r;
    r  <- head witness xs;
    xs <- behead xs;
    return r;
  }
}.

module G (S : Sampler) (A : Adv) = {
  proc main(p_val: param_t): bool = {
    var r;

    S.init(p_val);
    r <@ A(S).main(p_val);
    return r;
  }
}.

(* -- Section: main exports ------------------------------------------------

   PROOF MAP.  [eq_pr_fresh_ref] is the composition of a chain of Pr
   equalities between [G(-, A)] games; each link below names the local
   lemma that proves it and the nature of the argument:

     Fresh                          the fresh sampler, one draw per query
       | [pr_Fresh_BCount]          composition of the upto-bad cluster:
       |     Fresh ≡ FreshC              [pr_Fresh_FreshC]     (add flag)
       |     BCount(Fresh) ≡ BCountB     [pr_BCount_BCountB]   (add flag)
       |     FreshC ≡ BCountB up to bad  [eq_FreshC_BCountB]   (upto-bad)
       |     bad has probability 0       [pr_FreshC_bad0]      (by A_bound)
     BCount(Fresh)                  fresh draws, guarded at N queries
       | [pr_BCount_ROlazy]         lockstep: query i reads RO cell (p, i)
     ROSampler(LRO)                 lazily-sampled indexed RO
       | [pr_ROlazy_ROeager]        eager sampling [FullEager.RO_LRO_D]
     ROSampler(RO)                  eagerly-sampled indexed RO
       | [pr_BCountRef_ROeager]     lockstep: cell (p, i) = i-th list entry
     BCount(Ref)                    pre-sampled list, guarded at N
       | [final byequiv]            guard at N = list exhaustion at N
     Ref                            pre-sampled list

   [eq_pr_fresh_ref_ev] then transports the equality to an arbitrary
   event over the boolean result (four cases; needs both games lossless,
   which is where [A_ll] earns its keep at the export surface).
   ------------------------------------------------------------------------- *)

section.

declare module A <: Adv { -Count, -Fresh, -Ref }.

declare axiom A_ll :
  forall (O <: Oracle { -A }),
    islossless O.get => islossless A(O).main.

declare axiom A_bound:
  hoare[ A(Count(Fresh)).main : Count.n = 0 ==> Count.n <= N ].

(* Bounded-Count wrapper: tick-and-call under a structural guard at N.
   Past N calls, returns [witness] — mirrors list exhaustion in Ref.
   Internal: consumers only ever see [Fresh], [Ref] and [Count]. *)
local module BCount (O : Sampler) : Sampler = {
  proc init(p) = {
    Count(O).init(p);
  }

  proc get() : out_t = {
    var r;

    r <- witness;
    if (Count.n < N) {
      r <@ Count(O).get();
    }
    return r;
  }
}.

local clone import PROM.FullRO as RF with
  type in_t    <- param_t * int,
  type out_t   <- out_t,
  op   dout    <- fun (ab : _ * _) => d ab.`1,
  type d_in_t  <- param_t,
  type d_out_t <- bool
proof *.
  
local module BadFlag = {
  var bad : bool
}.

local module FreshC : Oracle = {
  proc init(p) = {
    BadFlag.bad <- false;
    Count.n <- 0;
    Fresh.init(p);
  }

  proc get() : out_t = {
    var r;

    r <- witness;
    if (Count.n < N) {
      Count.n <- Count.n + 1;
      r <@ Fresh.get();
    } else {
      BadFlag.bad <- true;
      r <@ Fresh.get();
    }
    return r;
  }
}.

local module BCountB : Oracle = {
  proc init(p) = {
    BadFlag.bad <- false;
    Count.n <- 0;
    Fresh.init(p);
  }

  proc get() : out_t = {
    var r;

    r <- witness;
    if (Count.n < N) {
      Count.n <- Count.n + 1;
      r <@ Fresh.get();
    } else {
      BadFlag.bad <- true;
    }
    return r;
  }
}.

local lemma pr_Fresh_FreshC (p_val : param_t) &m :
  Pr[G(Fresh, A).main(p_val) @ &m : res] =
  Pr[G(FreshC, A).main(p_val) @ &m : res].
proof.
byequiv => //; proc.
call (_: ={Fresh.p}).
+ proc *; inline *.
  by sp; if{2}; auto.
by inline*; auto.
qed.

local lemma pr_BCount_BCountB (p_val : param_t) &m :
  Pr[G(BCount(Fresh), A).main(p_val) @ &m : res] =
  Pr[G(BCountB, A).main(p_val) @ &m : res].
proof.
byequiv => //; proc.
call (_: ={Fresh.p, Count.n}).
+ by proc; inline *; sp; if; auto.
by inline *; auto.
qed.

local equiv eq_FreshC_BCountB:
  G(FreshC, A).main ~ G(BCountB, A).main: ={glob A, arg} ==> ={BadFlag.bad} /\ (!BadFlag.bad{2} => ={res}).
proof.
proc.
call (: BadFlag.bad
      , ={BadFlag.bad, Fresh.p, Count.n}
      , ={BadFlag.bad}).
+ exact: A_ll.
+ proc; sp; if=> //.
  + by inline *; auto.
  + inline *; auto=> |>.
    by move=> &0 _ _; exact: d_ll.
  + move=> &2 bad; proc; inline *.
    by sp; if; auto=> |>; smt(d_ll).
  + move=> &1; proc; inline *.
    by sp; if; auto=> |>; smt(d_ll).
by inline *; auto=> |> /#.
qed.

local lemma pr_FreshC_BCountB_good (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : res /\ !BadFlag.bad] =
  Pr[G(BCountB, A).main(p_val) @ &m : res /\ !BadFlag.bad].
proof. by byequiv eq_FreshC_BCountB=> /#. qed.

local lemma pr_FreshC_BCountB_bad (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : BadFlag.bad] =
  Pr[G(BCountB, A).main(p_val) @ &m : BadFlag.bad].
proof. by byequiv eq_FreshC_BCountB=> /#. qed.

local lemma pr_FreshC_bad0 (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : BadFlag.bad] = 0%r.
proof. 
have hub :
  Pr[G(FreshC, A).main(p_val) @ &m : BadFlag.bad] <=
  Pr[G(Count(Fresh), A).main(p_val) @ &m : N < Count.n].
+ byequiv (: ={glob A, arg} ==> BadFlag.bad{1} => N < Count.n{2}) => //; proc.
  sp; call(: ={Fresh.p}
          /\ Count.n{1} <= Count.n{2}
          /\ Count.n{1} <= N
          /\ (BadFlag.bad{1} => N < Count.n{2})).
  + proc; inline Fresh.get.
    seq 1 0 : #pre; 1: by auto.
    if {1}; auto; 1:smt().
    by auto=> /#.
  by inline *; auto; smt(N_ge0).
have hzero : Pr[G(Count(Fresh), A).main(p_val) @ &m : N < Count.n] = 0%r.
+ byphoare => //; hoare.
  proc; call A_bound; inline *; auto.
  smt(mu_bounded).
smt(mu_bounded).
qed.

local lemma pr_FreshC_resbad0 (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : res /\ BadFlag.bad] = 0%r.
proof.
suff: Pr[G(FreshC, A).main(p_val) @ &m: res /\ BadFlag.bad]
   <= Pr[G(FreshC, A).main(p_val) @ &m: BadFlag.bad].
+ by rewrite (pr_FreshC_bad0 p_val &m); smt(ge0_mu).
by rewrite Pr[mu_sub].
qed.

local lemma pr_BCountB_bad0 (p_val : param_t) &m :
  Pr[G(BCountB, A).main(p_val) @ &m : BadFlag.bad] = 0%r.
proof.
by rewrite -(pr_FreshC_BCountB_bad p_val &m) (pr_FreshC_bad0 p_val &m).
qed.

local lemma pr_BCountB_resbad0 (p_val : param_t) &m :
  Pr[G(BCountB, A).main(p_val) @ &m : res /\ BadFlag.bad] = 0%r.
proof.
suff: Pr[G(BCountB, A).main(p_val) @ &m: res /\ BadFlag.bad]
   <= Pr[G(BCountB, A).main(p_val) @ &m: BadFlag.bad].
+ by rewrite (pr_BCountB_bad0 p_val &m) #smt:(ge0_mu).
by rewrite Pr[mu_sub].
qed.

local lemma pr_Fresh_BCount (p_val : param_t) &m :
  Pr[G(Fresh, A).main(p_val) @ &m : res] =
  Pr[G(BCount(Fresh), A).main(p_val) @ &m : res].
proof.
rewrite (pr_Fresh_FreshC p_val &m).
rewrite (pr_BCount_BCountB p_val &m).
rewrite Pr[mu_split BadFlag.bad].
rewrite eq_sym Pr[mu_split BadFlag.bad] eq_sym.
congr.
+ by rewrite (pr_BCountB_resbad0 p_val &m) (pr_FreshC_resbad0 p_val &m).
exact: pr_FreshC_BCountB_good.
qed.

local module ROSampler (O : RO) = {
  proc init(p) = {
    var i;

    Fresh.p <- p;
    Count.n <- 0;
    O.init();
    
    i <- 0;
    while (i < N) {
      O.sample(p, i);
      i <- i + 1;
    }
  }

  proc get() = {
    var r;

    if (Count.n < N) {
      r <@ O.get(Fresh.p, Count.n);
      Count.n <- Count.n + 1;
    } else {
      r <- witness;
    }
    return r;
  }
}.

local lemma pr_BCount_ROlazy p_val &m:
    Pr[G(BCount(Fresh), A).main(p_val) @ &m: res]
  = Pr[G(ROSampler(LRO), A).main(p_val) @ &m: res].
proof.
byequiv=> //; proc.
call (: ={Fresh.p, Count.n}
     /\ (0 <= Count.n){2}
     /\ (forall i, 0 <= i < Count.n <=> (Fresh.p, i) \in RO.m){2}).
+ proc; sp; if; auto=> //.
  inline *.
  rcondt {2} 3; 1:by auto=> /#.
  auto=> |> &2 ge0_n inv n_lt_N r _.
  rewrite get_set_sameE //=.
  by split=> [/#|i]; rewrite !mem_set // -inv //= /#.
inline *.
kill {2} 6.
+ while (true) (N - i).
  + by auto=> |> &2 /#.
  by auto=> |> /#.
by auto=> |>; smt(emptyE).
qed.

local clone DList.ParametricProgram with
  type t <- out_t
proof *.

local module RODist (RO : RO) = {
  proc distinguish = G(ROSampler(RO), A).main
}.

local lemma pr_ROlazy_ROeager p_val &m:
    Pr[G(ROSampler(LRO), A).main(p_val) @ &m: res]
  = Pr[G(ROSampler(RO), A).main(p_val) @ &m: res].
proof.
rewrite eq_sym.
byequiv (: ={glob A, glob RO, glob Count, glob Fresh, arg} ==> _)=> //.
conseq (FullEager.RO_LRO_D RODist _)=> |>.
by move=> [] |> +; exact: d_ll.
qed.

local lemma pr_BCountRef_ROeager p_val &m:
    Pr[G(BCount(Ref), A).main(p_val) @ &m: res]
  = Pr[G(ROSampler(RO), A).main(p_val) @ &m: res].
proof.
byequiv=> //; proc.
call (: ={Count.n}
     /\ (0 <= Count.n <= N){1}
     /\ (forall i, Count.n{2} <= i < N
                => RO.m.[Fresh.p, i]{2} = Some (nth witness Ref.xs{1} (i - Count.n){2}))
     /\ (forall i, 0 <= i < N <=> (Fresh.p, i) \in RO.m){2}).
+ proc; sp; if; auto=> //.
  inline *; rcondf {2} 3; 1:by auto=> /#.
  auto=> |> &1 &2 ge0_count _ inv dom_ro count_lt_N.
  rewrite d_ll inv //= nth0_head=> /= _ _.
  smt(nth_behead).
inline *; wp; sp.
conseq (: _ ==> (forall i, 0 <= i < N
                       <=> RO.m.[Fresh.p, i]{2} = Some (nth witness Ref.xs i){1})
             /\ (forall i, 0 <= i < N <=> (Fresh.p, i) \in RO.m){2}).
+ by auto=> |>; smt(N_ge0).
proc change {1} 1: [ (i: int) (r0: out_t) ]
{
  Ref.xs <- [];
  i <- 0;
  while (i < N) {
    r0 <$ d p1;
    Ref.xs <- Ref.xs ++ [r0];
    i <- i + 1;
  }
}.
+ outline {1} 1 ~ ParametricProgram.Sample.sample.
  rewrite equiv [{1} 1 ParametricProgram.Sample_LoopSnoc_eq].
  inline {1} ^Ref.xs<@.
  by wp; while (={i} /\ l{1} = Ref.xs{2} /\ n{1} = N /\ d{1} = BoundedPreSample.d p1{2}); auto.
while (={i}
    /\ p1{1} = p{2}
    /\ (p = Fresh.p){2}
    /\ (size Ref.xs = i){1}
    /\ (forall j, 0 <= j < i{2} <=> RO.m.[Fresh.p, j]{2} = Some (nth witness Ref.xs j){1})
    /\ (0 <= i <= N){1}
    /\ (forall j, 0 <= j < i <=> (Fresh.p, j) \in RO.m){2}).
+ rcondt {2} 4; 1:by auto=> /#.
  auto=> |> &1 &2 inv ge0_i _ dom_ro i_lt_N r _.
  split; 1:by rewrite size_cat.
  split=> [j|]; 2:split=> [/#|j].
  + by rewrite get_setE cats1 nth_rcons; case: (j = size Ref.xs{1})=> |> /#.
  by rewrite mem_set; case: (j = size Ref.xs{1})=> |> /#.
by auto=> |>; smt(N_ge0 emptyE).
qed.

lemma eq_pr_fresh_ref p_val &m:
    Pr[G(Fresh, A).main(p_val) @ &m: res]
  = Pr[G(Ref,   A).main(p_val) @ &m: res].
proof.
rewrite (pr_Fresh_BCount _ &m).
rewrite (pr_BCount_ROlazy _ &m).
rewrite (pr_ROlazy_ROeager _ &m).
rewrite -(pr_BCountRef_ROeager _ &m).
byequiv=> //.
proc; inline *.
call (: ={glob Ref} /\ 0 <= Count.n{1} <= N /\ size Ref.xs{1} = N - Count.n{1}).
+ proc; inline *.
  auto=> |> &1 &2 ge0_count size_le_count size_count; split.
  + by rewrite size_behead /#.
  smt(size_eq0).
by auto=> |> xs; rewrite supp_dlist 1:N_ge0 N_ge0=> - [] ->.
qed.

(* Event-generic export.  [Fresh] and [Ref] are only Pr-equal (the internal
   chain crosses an upto-bad step), so a per-event Pr equality is the
   strongest exportable form; over the boolean result the four possible
   events reduce to [res], [!res] (via losslessness of both games, which
   is where [A_ll] earns its keep at the export surface), [true], and
   [false]. *)
lemma eq_pr_fresh_ref_ev (E : bool -> bool) p_val &m:
    Pr[G(Fresh, A).main(p_val) @ &m: E res]
  = Pr[G(Ref,   A).main(p_val) @ &m: E res].
proof.
have F_ll : Pr[G(Fresh, A).main(p_val) @ &m : true] = 1%r.
+ byphoare => //; proc; call (A_ll Fresh _); 1: by proc; auto; smt(d_ll).
  by inline *; auto.
have R_ll : Pr[G(Ref, A).main(p_val) @ &m : true] = 1%r.
+ byphoare => //; proc; call (A_ll Ref _); 1: by proc; auto.
  by inline *; auto; smt(dlist_ll d_ll N_ge0).
have base := eq_pr_fresh_ref p_val &m.
case (E true) => Et; case (E false) => Ef.
+ have -> : Pr[G(Fresh, A).main(p_val) @ &m : E res]
          = Pr[G(Fresh, A).main(p_val) @ &m : true] by rewrite Pr[mu_eq] // /#.
  have -> : Pr[G(Ref, A).main(p_val) @ &m : E res]
          = Pr[G(Ref, A).main(p_val) @ &m : true] by rewrite Pr[mu_eq] // /#.
  by rewrite F_ll R_ll.
+ have -> : Pr[G(Fresh, A).main(p_val) @ &m : E res]
          = Pr[G(Fresh, A).main(p_val) @ &m : res] by rewrite Pr[mu_eq] // /#.
  have -> : Pr[G(Ref, A).main(p_val) @ &m : E res]
          = Pr[G(Ref, A).main(p_val) @ &m : res] by rewrite Pr[mu_eq] // /#.
  exact base.
+ have -> : Pr[G(Fresh, A).main(p_val) @ &m : E res]
          = Pr[G(Fresh, A).main(p_val) @ &m : !res] by rewrite Pr[mu_eq] // /#.
  have -> : Pr[G(Ref, A).main(p_val) @ &m : E res]
          = Pr[G(Ref, A).main(p_val) @ &m : !res] by rewrite Pr[mu_eq] // /#.
  by rewrite Pr[mu_not] Pr[mu_not] F_ll R_ll base.
have -> : Pr[G(Fresh, A).main(p_val) @ &m : E res]
        = Pr[G(Fresh, A).main(p_val) @ &m : false] by rewrite Pr[mu_eq] // /#.
have -> : Pr[G(Ref, A).main(p_val) @ &m : E res]
        = Pr[G(Ref, A).main(p_val) @ &m : false] by rewrite Pr[mu_eq] // /#.
by rewrite Pr[mu_false] Pr[mu_false].
qed.

end section.

end BoundedPreSample.
