(* ==========================================================================

   BoundedPreSample: presampling library for bounded-query sequential
   adversaries, parametric over a secret parameter [p : param_t].

   Exports a single probability equivalence between:
     - G_Bounded: A run against a bounded fresh-sampler (BCount-guarded),
     - G_PreSampled: A run against a pre-sampled list of N draws.

   Both games share the BCount structural guard [if Count.n < N], so the
   oracle-call-count bound matches list exhaustion — no upto-bad, no
   asymmetric-tick issues.  Consumers that want to relate a bare fresh
   sampler to G_Bounded thread their own A_bound axiom at the outer
   site (e.g., via Pr[bad]=0 under A_bound and a standard Pr-slice
   argument).  This library is agnostic to that bridge.

   Module-type sharing: [Oracle] and [Adv] are declared in a nested
   sub-theory [Iface], which is cloned into the main theory.  Consumers
   that clone [BoundedPreSample] multiple times (e.g., for different
   distributions [d1], [d2]) can share a single external [Iface] clone
   across all uses via [theory I <- ...] substitution, preserving the
   nominal identity of [Oracle]/[Adv] across the clones.

   Typical use: clone this theory, instantiate d/d_param/N, compose the
   public [pr_bounded_eq_presampled] lemma with downstream reasoning on
   the pre-sampled list (e.g., RDiv.DistinguisherList for Rényi-∞,
   or direct coupling arguments).

   ========================================================================== *)

require import AllCore List Distr DList FMap.
require import FinType.

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

op [lossless] d_param : param_t distr.

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

(* Bounded-Count wrapper: tick-and-call under a structural guard at N.
   Past N calls, returns [witness] — mirrors list exhaustion in Ref. *)
module BCount (O : Sampler) : Sampler = {
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

(* -- Public modules ------------------------------------------------------- *)

(* Fresh sampler (parameter-aware).  The parameter [p] is set by the
   enclosing game (e.g., G_Bounded.main) before A is invoked. *)
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

(* -- Section: main exports ------------------------------------------------ *)

section.

declare module A <: Adv { -Count, -Fresh, -Ref }.

declare axiom A_ll :
  forall (O <: Oracle { -A }),
    islossless O.get => islossless A(O).main.

declare axiom A_bound:
  hoare[ A(Count(Fresh)).main : Count.n = 0 ==> Count.n <= N ].

local clone import PROM.FullRO as RF with
  type in_t    <- param_t * int,
  type out_t   <- out_t,
  op   dout    <- fun (ab : _ * _) => d ab.`1,
  type d_in_t  <- param_t,
  type d_out_t <- bool
proof *.
  
local lemma A_bound_BCount :
  hoare[ A(BCount(Fresh)).main : Count.n = 0 ==> Count.n <= N ].
proof.
proc (Count.n <= N).
+ smt(N_ge0).
+ smt().
+ proc; sp; if; auto.
  by inline *; auto=> |> /#.
qed.

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

local lemma pr_fresh_eq_freshC (p_val : param_t) &m :
  Pr[G(Fresh, A).main(p_val) @ &m : res] =
  Pr[G(FreshC, A).main(p_val) @ &m : res].
proof.
byequiv => //; proc.
call (_: ={Fresh.p}).
+ proc *; inline *.
  by sp; if{2}; auto.
by inline*; auto.
qed.

local lemma pr_bounded_eq_BCountB (p_val : param_t) &m :
  Pr[G(BCount(Fresh), A).main(p_val) @ &m : res] =
  Pr[G(BCountB, A).main(p_val) @ &m : res].
proof.
byequiv => //; proc.
call (_: ={Fresh.p, Count.n}).
+ by proc; inline *; sp; if; auto.
by inline *; auto.
qed.

local equiv eq_freshC_BCountB:
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

local lemma pr_freshC_eq_BCountB (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : res /\ !BadFlag.bad] =
  Pr[G(BCountB, A).main(p_val) @ &m : res /\ !BadFlag.bad].
proof. by byequiv eq_freshC_BCountB=> /#. qed.

local lemma pr_bad_freshC_eq_BCountB (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : BadFlag.bad] =
  Pr[G(BCountB, A).main(p_val) @ &m : BadFlag.bad].
proof. by byequiv eq_freshC_BCountB=> /#. qed.

local lemma pr_freshC_bad (p_val : param_t) &m :
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

local lemma pr_freshC_resbad (p_val : param_t) &m :
  Pr[G(FreshC, A).main(p_val) @ &m : res /\ BadFlag.bad] = 0%r.
proof.
suff: Pr[G(FreshC, A).main(p_val) @ &m: res /\ BadFlag.bad] <= 0%r.
+ smt(ge0_mu).
rewrite -(pr_freshC_bad p_val &m).
by byequiv (: _ ==> ={BadFlag.bad})=> //; sim.
qed.

local lemma pr_BCountB_bad (p_val : param_t) &m :
  Pr[G(BCountB, A).main(p_val) @ &m : BadFlag.bad] = 0%r.
proof.
by rewrite -(pr_bad_freshC_eq_BCountB p_val &m) (pr_freshC_bad p_val &m).
qed.

local lemma pr_BCountB_resbad (p_val : param_t) &m :
  Pr[G(BCountB, A).main(p_val) @ &m : res /\ BadFlag.bad] = 0%r.
proof.
suff: Pr[G(BCountB, A).main(p_val) @ &m: res /\ BadFlag.bad]
   <= Pr[G(BCountB, A).main(p_val) @ &m: BadFlag.bad].
+ by rewrite (pr_BCountB_bad p_val &m) #smt:(ge0_mu).
by byequiv=> //; conseq (: _ ==> ={BadFlag.bad})=> //; sim.
qed.

local lemma pr_fresh_eq_bounded (p_val : param_t) &m :
  Pr[G(Fresh, A).main(p_val) @ &m : res] =
  Pr[G(BCount(Fresh), A).main(p_val) @ &m : res].
proof.
rewrite (pr_fresh_eq_freshC p_val &m).
rewrite (pr_bounded_eq_BCountB p_val &m).
rewrite Pr[mu_split BadFlag.bad].
rewrite eq_sym Pr[mu_split BadFlag.bad] eq_sym.
congr.
+ by rewrite (pr_BCountB_resbad p_val &m) (pr_freshC_resbad p_val &m).
exact: pr_freshC_eq_BCountB.
qed.

local module Wobble (O : RO) = {
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

local lemma eq_freshB_wobbleL p_val &m:
    Pr[G(BCount(Fresh), A).main(p_val) @ &m: res]
  = Pr[G(Wobble(LRO), A).main(p_val) @ &m: res].
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

local module R (RO : RO) = {
  proc distinguish = G(Wobble(RO), A).main
}.

local lemma eq_wobbleL_wobbleE p_val &m:
    Pr[G(Wobble(LRO), A).main(p_val) @ &m: res]
  = Pr[G(Wobble(RO), A).main(p_val) @ &m: res].
proof.
rewrite eq_sym.
byequiv (: ={glob A, glob RO, glob Count, glob Fresh, arg} ==> _)=> //.
conseq (FullEager.RO_LRO_D R _)=> |>.
by move=> [] |> +; exact: d_ll.
qed.

local lemma eq_refB_wobbleE p_val &m:
    Pr[G(BCount(Ref), A).main(p_val) @ &m: res]
  = Pr[G(Wobble(RO), A).main(p_val) @ &m: res].
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
rewrite (pr_fresh_eq_bounded _ &m).
rewrite (eq_freshB_wobbleL _ &m).
rewrite (eq_wobbleL_wobbleE _ &m).
rewrite -(eq_refB_wobbleE _ &m).
byequiv=> //.
proc; inline *.
call (: ={glob Ref} /\ 0 <= Count.n{1} <= N /\ size Ref.xs{1} = N - Count.n{1}).
+ proc; inline *.
  auto=> |> &1 &2 ge0_count size_le_count size_count; split.
  + by rewrite size_behead /#.
  smt(size_eq0).
by auto=> |> xs; rewrite supp_dlist 1:N_ge0 N_ge0=> - [] ->.
qed.

(*
Remaining to do:
- Generalize stdlib's DList procedure-based sampling to work with
  parameterized distributions; (breaking change pending release)
- Fix proc change bug;
- Generalize the overall result here to avoid having to bound up
  front. (Equivalence between lazy sampling, and eagerly-sampled
  prefix + lazy.)
*)

end section.

end BoundedPreSample.
