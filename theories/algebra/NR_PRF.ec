(* NR-PRF *)
require import Int Real List SmtMap Distr FSet.
require (*--*) GroupAction PRF Word BitWord.
require import PROM DList Dexcepted Mu_mem.

require (*--*) FelTactic.

(* We need a regular, effective, abelian group action for this construction *)
clone import GroupAction.ARegEGA as Ega.

(* This function should compute the action of a list of group elements masked by an equal sized list of booleans *)
op compute_action (gs : group list) (ss : bool list) (x : set) : set =
    with gs = "[]"     ,      ss = "[]" => x
    with gs = "[]"     , ss = (::) s ss => x
    with gs = (::) g gs,      ss = "[]" => x
    with gs = (::) g gs, ss = (::) s ss =>
      if s then compute_action gs ss (act g x)
           else compute_action gs ss x.

op l : {int | 0 < l} as gt0_l.

clone import Word as GroupWord with
  type Alphabet.t <- group,
  op n <- l + 1
proof
 ge0_n by smt(gt0_l)
rename
  "word" as "key"
  "dunifin" as "dkey".

clone import BitWord as S with
  op n <- l
proof
  ge0_n by smt(gt0_l)
rename
  "word" as "bits".

(* Setup keyspace, domain, and range *)
type K = key.
type D = bits.
type R = set.

(* This is the Naor-style PRF construction *)
op F (k : K) (m : D) = compute_action (behead (ofkey k)) (ofbits m) (act k.[0] x0).

(* Setup the uniform distribution on our range *)
clone import MFinite as Uni_dR with
  type t <- R
rename
  "dunifin" as "dR".

(* Setting up the PRF *)
clone import PRF as PRF_t with
  type D <- D,
  type R <- R.

clone import RF as NS_RF with
  op dR _ <- dR
proof *.
realize dR_ll.
by move=> _; exact dR_ll.
qed.

clone import PseudoRF as NS_PRF with
  type K <- K,
  op dK <- dmap (dlist sample (l + 1)) mkkey,
  op F <- F
proof *.
realize dK_ll.
exact/dmap_ll/dlist_ll/DG.dunifin_ll.
qed.

(* A very useful lemma that shows that dR ~= sample *)
lemma sample_dR_iso g x: mu1 sample g = mu1 dR (act g x).
proof.
have /= <- := dmap1E_can dR (extract x) (fun g=> act g x) g _ _.
+ by rewrite /cancel=> g'; rewrite -extractUniq.
+ by move=> a _ /=; rewrite extractP.
congr; apply: eq_funi_ll.
+ exact: DG.dunifin_funi.
+ exact: DG.dunifin_ll.
+ apply/dmap_funi.
  + exists (fun g=> act g x); split.
    + by move=> a; exact: extractP.
    by move=> h; rewrite -extractUniq.
  exact: dR_funi.
exact/dmap_ll/Uni_dR.dR_ll.
qed.

(* ----------------------------------------------- *)
(* Weak pseudorandomness assumption *)
module type WP = {
  proc init() : unit
  proc query() : R * R
}.

module type WP_Oracles = {
  proc query() : R * R
}.

module type WP_Adv (F : WP_Oracles) = {
  proc distinguish (_ : int) : bool
}.

module WP_IND (F : WP) (A : WP_Adv) = {
  proc main(J : int) : bool = {
    var b : bool;

         F.init();
    b <@ A(F).distinguish(J);
    return b;
  }
}.

module WP_Real = {
  var g : group

  proc init() = {
    g <$ sample;
  }

  proc query() = {
    var xq, yq : set;

    xq <$ dR;
    yq <- act g xq;
    return (xq, yq);
  }
}.

module WP_Ideal = {
  var m  : (set, set) fmap

  proc init() = {
    m <- empty;
  }

  proc query() = {
    var xq, yq : set;
  
    xq <$ dR;
    if (xq \notin m) {
          yq <$ dR \ (rng m);
      m.[xq] <- yq;
    }
    return (xq, oget m.[xq]);
  }
}.

abstract theory WPRF.
module WF = {
  var m : (set, set) fmap
  var bad : bool

  proc init() = {
      m <- empty;
    bad <- false;
  }

  proc query() = {
    var xq, yq : set;

    xq <$ dR;
    yq <$ dR;
    if (xq \notin m) {
      m.[xq] <- yq;
    } else {
       bad <- true;
    }
    return (xq, oget m.[xq]);
  }
}.

module WS = {
  var xs : set list

  proc init() = {
    xs <- [];
  }

  proc query() = {
    var xq, yq : set;

    xq <$ dR;
    yq <$ dR;
    xs <- xq :: xs; (** Detect collisions **)
    return (xq, yq);
  }
}.

module CountWP (WP : WP) = {
  var c : int

  proc init() = {
         WP.init();
    c <- 0;
  }

  proc query() = {
    var r;

    r <@ WP.query();
    c <- c + 1;
    return r;
  }
}.

op q : { int | 0 <= q } as ge0_q.

section WPRF_Security.
declare module D : WP_Adv { WP_Real, WP_Ideal, WF, CountWP }.

axiom D_Count (WP <: WP { D, CountWP }) c0:
  hoare [D(CountWP(WP)).distinguish: CountWP.c = c0 ==> CountWP.c <= c0 + q].

axiom D_ll (WP <: WP_Oracles { D }):
     islossless WP.query
  => islossless D(WP).distinguish.

local module WP_BIND (WP : WP) = {
  module O = {
    proc query() = {
      var r <- witness;

      if (CountWP.c < q) {
                r <- WP.query();
        CountWP.c <- CountWP.c + 1;
      }
      return r;
    }
  }

  proc main(J : int) = {
    var r;

         CountWP(WP).init();
    r <@ D(O).distinguish(J);
    return r;
  }
}.

local lemma WP_Bounded (WP <: WP { D, CountWP }):
     islossless WP.query
  => equiv [WP_IND(WP, D).main ~ WP_BIND(WP).main:
              ={glob D, glob WP, arg} ==> ={glob D, glob WP, res}].
proof.
move=> WP_query_ll.
proc.
call (: ={glob D, glob WP, arg} /\ CountWP.c{2} = 0 ==> ={glob D, glob WP, res}).
+ transitivity
    D(CountWP(WP)).distinguish
    (={glob D, glob WP, arg} /\ CountWP.c{2} = 0 ==> ={glob D, glob WP, res})
    (={glob D, glob WP, glob CountWP, arg} /\ CountWP.c{1} = 0 ==> ={glob D, glob WP, res})=> />.
  + by move=> &2; exists (glob D){2} (glob WP){2} 0 (arg{2}).
  + proc (={glob WP})=> //.
    by proc *; inline *; sim.
  conseq (: CountWP.c{1} <= q => ={glob D, glob WP, res}) (: CountWP.c = 0 ==> CountWP.c <= 0 + q)=> //.
  + exact: (D_Count WP 0).
  symmetry.
  proc (q < CountWP.c) (={glob WP, glob CountWP})=> />.
  + smt().
  + exact: D_ll.
  + proc; sp; if {1}.
    + by conseq (: ={r, glob WP, CountWP.c})=> //; inline *; sim.
    conseq (: true) _ (: CountWP.c = q ==> q < CountWP.c)=> /> => [/#||].
    + by wp; conseq (: true)=> /> => [/#|]; auto.
    by wp; call {2} WP_query_ll.
  + move=> _ _; proc; sp; if; auto.
    by inline *; auto; call WP_query_ll.
  by proc; wp; call WP_query_ll; auto=> /#.
by inline *; auto; call (: true).
qed.

local lemma WF_pr_coll &m j:
     Pr[WP_BIND(WF).main(j) @ &m: exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y]
  <= (q * (q - 1))%r / (2 * Support.card)%r.
proof.
fel 1 (CountWP.c)
    (fun i=> i%r / Support.card%r)
    q
    (exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y)
    [WP_BIND(WF).O.query: (CountWP.c < q)]
    (0 <= card (frng WF.m) <= CountWP.c <= q)=> />.
+ rewrite -(StdBigop.Bigreal.BRA.big_distrl _ _ (fun i=> i%r))=> //.
  + smt().
  by rewrite StdBigop.Bigreal.sumidE 1:ge0_q /#.
+ inline *; auto=> />; rewrite frng0 fcards0 ge0_q //=.
  by rewrite negb_exists=> x /=; rewrite emptyE.
+ proc; inline *; sp 1; if=> //.
  wp; rnd (mem (frng WF.m)); auto=> /> &0 ge0_c c_lt_q nocoll ge0_rng rng_le_c _.
  move=> xq _; split=> [|_ yq _].
  + rewrite (mu_mem (frng WF.m{0}) dR (1%r / Support.card%r) _).
    + by move=> x _; rewrite dR1E.
    smt(Support.card_gt0).
  rewrite domE=> /= m_xq x x' y x_neq_x'.
  rewrite !get_setE mem_frng; case: (x = xq)=> [/>|_]; case: (x' = xq)=> [/>|_ m_x'|/> m_x|_].
  + by rewrite /rng; exists x'.
  + by rewrite /rng; exists x.
  move: nocoll=> /negb_exists /(_ x) /= /negb_exists /(_ x') /= /negb_exists /(_ y) /=.
  by rewrite x_neq_x' /= negb_and=> - [].
+ move=> c; proc; sp; if=> //; inline *; auto=> />.
  move=> &0 c_lt_q ge0_card card_le_c _ xq _ yq _.
  split=> [|/#].
  rewrite domE=> /= m_xq.
  + rewrite fcard_ge0 /=; split=> [/#|]; split=> [|/#].
    rewrite frng_set fcardU fcard1.
    move: (subset_leq_fcard (frng (rem WF.m{0} xq)) (frng WF.m{0}) _).
    + move=> x; rewrite !mem_frng /rng=> /> x'.
      by rewrite remE; case: (x' = xq)=> /> _ m_x'; exists x'.
    smt(fcard_ge0).
by move=> b c; proc; rcondf 2; auto.
qed.

local module WRP_bad = {
  var m   : (set, set) fmap
  var bad : bool

  proc init() = {
      m <- empty;
    bad <- false;
  }

  proc query() = {
    var xq, yq : set;
  
    xq <$ dR;
    if (xq \notin m) {
      yq <$ dR;
      if (rng m yq) {
        bad <- true;
         yq <$ dR \ (rng m);
      }
      m.[xq] <- yq;
    }
    return (xq, oget m.[xq]);
  }
}.

local clone import TwoStepSampling with
  type    i <- unit,
  type    t <- set,
    op dt _ <- dR.

local equiv WP_Ideal_bad_query:
  WP_Ideal.query ~ WRP_bad.query:
    ={m}(WP_Ideal, WRP_bad)
    ==> ={res} /\ ={m}(WP_Ideal, WRP_bad).
proof.
proc.
seq  1  1: (={xq} /\ #pre).
+ by auto.
if=> //.
transitivity {1}
  { yq <@ S.direct((), fun _=> rng WP_Ideal.m); WP_Ideal.m <- WP_Ideal.m.[xq <- yq]; }
  (={xq, WP_Ideal.m} ==> ={xq, yq, WP_Ideal.m})
  (={xq} /\ WP_Ideal.m{1} = WRP_bad.m{2} ==> ={xq, yq} /\ WP_Ideal.m{1} = WRP_bad.m{2})=> // [/#||].
+ by inline *; auto.
transitivity {2}
  { yq <@ S.indirect((), fun _=> rng WRP_bad.m); WRP_bad.m <- WRP_bad.m.[xq <- yq]; }
  (={xq} /\ WP_Ideal.m{1} = WRP_bad.m{2} ==> ={xq, yq} /\ WP_Ideal.m{1} = WRP_bad.m{2})
  (={xq, WRP_bad.m} ==> ={xq, yq, WRP_bad.m})=> // [/#||].
+ by wp; call ll_direct_indirect_eq; auto; rewrite dR_ll.
inline *; sp.
seq  1  1: (r{1} = yq{2} /\ #pre); first by auto.
by if=> //; auto.
qed.

(** TODO: This should be moved out of PRP and somewhere more accessible **)
lemma leq_card_rng_dom (m:('a,'b) fmap):
  card (frng m) <= card (fdom m).
proof.
elim/fset_ind: (fdom m) {-2}m (eq_refl (fdom m))=> {m} [m /fdom_eq0 ->|].
+ by rewrite frng0 fdom0 !fcards0.
move=> x s x_notin_s ih m dom_m.
have ->: m = (rem m x).[x <- oget m.[x]].
+ apply/fmap_eqP=> x'; rewrite get_setE remE; case: (x' = x)=> [->>|//].
  have /fsetP /(_ x):= dom_m; rewrite in_fsetU in_fset1 /= mem_fdom domE.
  by case: m.[x].
have ->: frng (rem m x).[x <- oget m.[x]] = frng (rem m x) `|` fset1 (oget m.[x]).
+ apply/fsetP=> y'; rewrite in_fsetU in_fset1 !mem_frng !rngE /=.
  split=> [[] a|].
  + rewrite get_setE remE; case: (a = x)=> [->>|a_neq_x ma_y'] />.
    by left; exists a; rewrite remE a_neq_x.
  case=> [[a]|->].
  + rewrite remE; case: (a = x)=> //= x_neq_a ma_y'.
    by exists a; rewrite get_setE remE x_neq_a.
  by exists x; rewrite get_set_sameE.
rewrite fcardU fsetI1 fun_if !fcard1 fcards0.
rewrite fdom_set fcardUI_indep 2:fcard1.
+ by apply/fsetP=> x0; rewrite in_fsetI fdom_rem !inE -andbA andNb.
rewrite StdOrder.IntOrder.ler_subl_addr; apply/StdOrder.IntOrder.ler_paddr.
+ by case: (mem (frng _) _).
apply/StdOrder.IntOrder.ler_add2r/ih/fsetP=> x0.
by rewrite fdom_rem dom_m !inE; case: (x0 = x).
qed.

lemma endo_dom_rng (m:('a,'a) fmap):
  (exists x, x \notin m) =>
  exists x, !rng m x.
proof.
elim=> x x_notin_m.
have h: 0 < card (((fdom m) `|` fset1 x) `\` (frng m)); last first.
+ have [a]: exists a, a \in (fdom m `|` fset1 x) `\` frng m.
  + have ->: forall b, b = !!b by done.
    rewrite negb_exists /= -negP=> /in_eq_fset0 h'.
    by move: h' h=> ->; rewrite fcards0.
  by rewrite in_fsetD mem_frng=> - [] _ a_notin_rng_m; exists a.
rewrite fcardD fcardUI_indep.
+ by apply/fsetP=> x'; rewrite !inE mem_fdom /#.
rewrite fcard1 fsetIUl fcardUI_indep.
+ by apply/fsetP=> x'; rewrite !inE mem_fdom /#.
have ->: card (fset1 x `&` frng m) = if x \in (frng m) then 1 else 0.
+ smt (@FSet).
by move: x_notin_m; rewrite -mem_fdom; smt (leq_card_rng_dom @FSet).
qed.

lemma nosmt notin_supportIP (P : 'a -> bool) (d : 'a distr):
  (exists a, support d a /\ !P a) <=> mu d P < mu d predT.
proof.
rewrite (@mu_split _ predT P) /predI /predT /predC /=.
rewrite (@exists_eq (fun a => support d a /\ !P a) (fun a => !P a /\ a \in d)) /=.
+ by move=> a /=; rewrite andbC.
by rewrite -(@witness_support (predC P)) -/(predC _) /#.
qed.

lemma excepted_lossless (m:(R,R) fmap):
  (exists x, x \notin m) =>
  is_lossless (dR \ rng m).
proof.
move=> /endo_dom_rng [x h]; rewrite dexcepted_ll 1:dR_ll //.
by rewrite -dR_ll; apply/notin_supportIP; exists x=> />; exact/dR_fu.
qed.
(** End of TODO **)

local equiv WRP_bad_WF:
  WP_IND(WRP_bad, D).main ~ WP_IND(WF, D).main:
    ={glob D}
    ==>    (WRP_bad.bad{1} <=> (exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y){2})
        /\ (!WRP_bad.bad{1} => ={res}).
proof.
symmetry; proc.
call (: WRP_bad.bad
      ,    ={m}(WF, WRP_bad)
        /\ !WRP_bad.bad{2}
        /\ (forall x x' y, WF.m.[x] = Some y => WF.m.[x'] = Some y => x = x'){1}
      , (WRP_bad.bad{2} <=> (exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y){1}))=> //.
+ exact: D_ll.
+ proc; seq  1  1: (={xq} /\ #pre); first by auto.
  if {2}.
  + rcondt {1} 2; first by auto.
    seq  1  1: (={yq} /\ #pre); first by auto.
    if {2}.
    + auto=> /> &2 not_bad2 not_bad1 xq_notin_m yq_in_m.
      split=> [|_].
      + by apply: excepted_lossless; exists xq{2}.
      move=> y _.
      move: yq_in_m=> @/rng [] x0 m_x0.
      move: xq_notin_m; rewrite domE=> /= m_xq.
      have neq_x: (x0 <> xq{2}).
      + rewrite -negP=> /(congr1 (fun x=> WRP_bad.m{2}.[x])) //=.
        by rewrite m_x0 m_xq.
      by exists x0 xq{2} yq{2}; rewrite !get_setE neq_x.
    auto=> /> &2 _ not_bad1 _ yq_notin_m x x' y.
    rewrite !get_setE; case: (x = xq{2})=> />; case: (x' = xq{2})=> />.
    + by move: yq_notin_m=> @/rng; rewrite negb_exists=> /= ->.
    + by case: (yq{2} = y)=> />; move: yq_notin_m=> @/rng; rewrite negb_exists=> /= ->.
    by move=> _ _; exact: not_bad1.
  by auto.
+ move=> &2 -> /=; proc; auto=> /> &0 x x' y x_neq_x' m_x m_x'.
  rewrite dR_ll=> //= xq _ _ yq _ _; rewrite domE=> /= m_xq.
  have neq_x: x <> xq.
  + by rewrite -negP=> /(congr1 (fun x=> WF.m{0}.[x])) /=; rewrite m_x m_xq.
  have neq_x': x' <> xq.
  + by rewrite -negP=> /(congr1 (fun x=> WF.m{0}.[x])) /=; rewrite m_x' m_xq.
  by exists x x' y; rewrite x_neq_x' !get_set_neqE.
+ move=> &1.
  conseq (: WRP_bad.bad ==> WRP_bad.bad)=> //.
  + proc; seq 1: WRP_bad.bad=> //.
    + by auto; rewrite dR_ll.
    + if=> //; seq 1: (WRP_bad.bad /\ xq \notin WRP_bad.m)=> //.
      + by auto; rewrite dR_ll.
      + if=> //; auto=> /> &0 _ xq_notin_m _.
        by apply: excepted_lossless; exists xq{0}.
      by hoare; conseq />.
    by hoare; conseq />.
by inline *; auto=> />; smt(emptyE).
qed.

local lemma WP_WF_pre_pr &m:
     `|  Pr[WP_IND(WP_Ideal, D).main() @ &m: res]
       - Pr[WP_IND(WF, D).main() @ &m: res]|
  <= Pr[WP_IND(WF, D).main() @ &m:
         exists x x' y,    x <> x'
                       /\ WF.m.[x] = Some y
                       /\ WF.m.[x'] = Some y].
proof.
have ->:   Pr[WP_IND(WP_Ideal, D).main() @ &m: res]
         = Pr[WP_IND(WRP_bad, D).main() @ &m: res].
+ byequiv (: ={glob D} ==> ={res})=> //.
  proc; call (: ={m}(WP_Ideal, WRP_bad)).
  + by conseq WP_Ideal_bad_query.
  by inline *; auto.
rewrite /(`|_|)%Real.
case: (0%r <= Pr[WP_IND(WRP_bad, D).main() @ &m: res] - Pr[WP_IND(WF, D).main() @ &m: res])=> _.
+ rewrite StdOrder.RealOrder.ler_subl_addl.
  by byequiv WRP_bad_WF=> /#.
rewrite RField.opprB StdOrder.RealOrder.ler_subl_addl.
+ have <-:   Pr[WP_IND(WRP_bad, D).main() @ &m: WRP_bad.bad]
           = Pr[WP_IND(WF, D).main() @ &m: exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y].
  + by byequiv WRP_bad_WF.
by byequiv=> //; symmetry; conseq WRP_bad_WF=> /#.
qed.

lemma WP_WF_pr &m:
     `|  Pr[WP_IND(WP_Real, D).main() @ &m: res]
       - Pr[WP_IND(WF, D).main() @ &m: res]|
  <=   `|  Pr[WP_IND(WP_Real, D).main() @ &m: res]
         - Pr[WP_IND(WP_Ideal, D).main() @ &m: res]|
     + (q * (q - 1))%r / (2 * Support.card)%r.
proof.
move: (WF_pr_coll &m).
have <-:   Pr[WP_IND(WF, D).main() @ &m: exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y]
         = Pr[WP_BIND(WF).main() @ &m: exists x x' y, x <> x' /\ WF.m.[x] = Some y /\ WF.m.[x'] = Some y].
+ byequiv (WP_Bounded WF _)=> //.
  by proc; auto; rewrite dR_ll.
move: (WP_WF_pre_pr &m).
smt().
qed.
end section WPRF_Security.

section WSample_Security.
declare module D : WP_Adv { WF, WS, CountWP }.

axiom D_Count (WP <: WP { D, CountWP }) c0:
  hoare [D(CountWP(WP)).distinguish: CountWP.c = c0 ==> CountWP.c <= c0 + q].

axiom D_ll (WP <: WP_Oracles { D }):
     islossless WP.query
  => islossless D(WP).distinguish.

local module WP_BIND (WP : WP) = {
  module O = {
    proc query() = {
      var r <- witness;

      if (CountWP.c < q) {
                r <- WP.query();
        CountWP.c <- CountWP.c + 1;
      }
      return r;
    }
  }

  proc main(J : int) = {
    var r;

         CountWP(WP).init();
    r <@ D(O).distinguish(J);
    return r;
  }
}.

local lemma WP_Bounded (WP <: WP { D, CountWP }):
     islossless WP.query
  => equiv [WP_IND(WP, D).main ~ WP_BIND(WP).main:
              ={glob D, glob WP, arg} ==> ={glob D, glob WP, res}].
proof.
move=> WP_query_ll.
proc.
call (: ={glob D, glob WP, arg} /\ CountWP.c{2} = 0 ==> ={glob D, glob WP, res}).
+ transitivity
    D(CountWP(WP)).distinguish
    (={glob D, glob WP, arg} /\ CountWP.c{2} = 0 ==> ={glob D, glob WP, res})
    (={glob D, glob WP, glob CountWP, arg} /\ CountWP.c{1} = 0 ==> ={glob D, glob WP, res})=> />.
  + by move=> &2; exists (glob D){2} (glob WP){2} 0 (arg{2}).
  + proc (={glob WP})=> //.
    by proc *; inline *; sim.
  conseq (: CountWP.c{1} <= q => ={glob D, glob WP, res}) (: CountWP.c = 0 ==> CountWP.c <= 0 + q)=> //.
  + exact: (D_Count WP 0).
  symmetry.
  proc (q < CountWP.c) (={glob WP, glob CountWP})=> />.
  + smt().
  + exact: D_ll.
  + proc; sp; if {1}.
    + by conseq (: ={r, glob WP, CountWP.c})=> //; inline *; sim.
    conseq (: true) _ (: CountWP.c = q ==> q < CountWP.c)=> /> => [/#||].
    + by wp; conseq (: true)=> /> => [/#|]; auto.
    by wp; call {2} WP_query_ll.
  + move=> _ _; proc; sp; if; auto.
    by inline *; auto; call WP_query_ll.
  by proc; wp; call WP_query_ll; auto=> /#.
by inline *; auto; call (: true).
qed.

local lemma WS_pr_coll &m j:
     Pr[WP_BIND(WS).main(j) @ &m: !uniq WS.xs]
  <= (q * (q - 1))%r / (2 * Support.card)%r.
proof.
fel 1 (CountWP.c)
    (fun i=> i%r / Support.card%r)
    q
    (!uniq WS.xs)
    [WP_BIND(WS).O.query: (CountWP.c < q)]
    (   0 <= size WS.xs <= CountWP.c <= q)=> />.
+ rewrite -(StdBigop.Bigreal.BRA.big_distrl _ _ (fun i=> i%r))=> //.
  + smt().
  by rewrite StdBigop.Bigreal.sumidE 1:ge0_q /#.
+ by inline *; auto=> />; rewrite ge0_q.
+ proc; inline *; sp 1; if=> //.
  wp; seq 1: (xq \in WS.xs) (CountWP.c%r / Support.card%r) 1%r _ 0%r (uniq WS.xs)=> //.
  + by auto.
  + rnd; auto=> /> &0 ge0_c c_lt_q uniq_xs ge0_sxs sxs_le_c _.
    move: (mu_mem_le_size (WS.xs{0}) dR (1%r / Support.card%r) _).
    + by move=> x _; rewrite dR1E.
    smt(Support.card_gt0).
  by hoare; auto.
+ by move=> c; proc; sp; if=> //; inline *; auto=> /#.
by move=> b c; proc; sp; if=> //; inline *; auto.
qed.

local equiv WS_WF:
  WP_IND(WF, D).main ~ WP_IND(WS, D).main:
    ={glob D, arg}
    ==>    (WF.bad{1} <=> !uniq WS.xs{2})
        /\ (uniq WS.xs{2} => ={res}).
proof.
proc.
call (: !uniq WS.xs
      ,    (forall x, x \in WF.m{1} <=> x \in WS.xs{2})
        /\ !WF.bad{1}
        /\ uniq WS.xs{2}
      , WF.bad{1} <=> !uniq WS.xs{2}).
+ exact: D_ll.
+ proc; auto=> /> &1 &2 xs_uniq dom_xs not_bad xq _ yq _.
  rewrite dom_xs=> />; rewrite get_set_sameE=> /= xq_notin_xs x.
  by rewrite mem_set dom_xs=> /=; case: (x = xq).
+ by move=> &2 -> /=; proc; auto; rewrite dR_ll.
+ by move=> &1; proc; auto; rewrite dR_ll=> />.
by inline *; auto=> />; split=> [|/#]; smt(emptyE).
qed.

local lemma WS_WF_pr &m j:
     `|  Pr[WP_IND(WS, D).main(j) @ &m: res]
       - Pr[WP_IND(WF, D).main(j) @ &m: res]|
  <= Pr[WP_IND(WS, D).main(j) @ &m: !uniq WS.xs].
proof.
rewrite /(`|_|)%Real.
case: (0%r <= Pr[WP_IND(WS, D).main(j) @ &m: res] - Pr[WP_IND(WF, D).main(j) @ &m: res])=> _.
+ have ->:   Pr[WP_IND(WS, D).main(j) @ &m: !uniq WS.xs]
           = Pr[WP_IND(WF, D).main(j) @ &m: WF.bad].
  + by rewrite eq_sym; byequiv WS_WF.
  rewrite StdOrder.RealOrder.ler_subl_addl.
  by byequiv=> //; symmetry; conseq WS_WF=> /#.
rewrite RField.opprB StdOrder.RealOrder.ler_subl_addl.
by byequiv WS_WF=> /#.
qed.

lemma WS_WF_pr &m:
     `|  Pr[WP_IND(WP_Real, D).main() @ &m: res]
       - Pr[WP_IND(WS, D).main() @ &m: res]|
  <=   `|  Pr[WP_IND(WP_Real, D).main() @ &m: res]
         - Pr[WP_IND(WF, D).main() @ &m: res]|
     + (q * (q - 1))%r / (2 * Support.card)%r.
proof.
move: (WS_pr_coll &m).
have <-:   Pr[WP_IND(WS, D).main() @ &m: !uniq WS.xs]
         = Pr[WP_BIND(WS).main() @ &m: !uniq WS.xs].
+ byequiv (WP_Bounded WS _)=> //.
  by proc; auto; rewrite dR_ll.
move: (WS_WF_pre_pr &m).
smt().
qed.

end section WSample_Security.
end WPRF.

(** Define the final reduction(s) **)
module Red (D : Distinguisher) (WP : WP_Oracles) = {
  var j : int
  var m : (bool list, R * R) fmap

  var gis : group list

  module O = {
    proc f(x) = {
      var xq, yq;
      var xs <- ofbits x;
      var  p <- take j xs;
      var  b <- nth witness xs j;
      var  s <- drop (j + 1) xs;
      var  r <- witness;

      if (p \notin m) {
        (xq, yq) <@ WP.query();
        m.[p] <- (xq, yq);
      }
      (xq, yq) <- oget m.[p];

      r <- compute_action gis s (if b then yq else xq);
      return r;
    }
  }

  proc distinguish(J) = {
    var b;
      m <- empty;
      j <- J;
    gis <$ dlist sample (l - j - 1);
      b <@ D(O).distinguish();
    return b;
  }
}.


section PRF_Security.
declare module D : Distinguisher { PRF, RF }.

(* ---------------------------------------------------------------------------------------- *)

(* The hybrid used for the proof of Theorem 4.19 *)
(* This hybrid slowly replaces each action of a gi on x0 with the random sampling of a set element *)
(* The 0th hybrid should exactly represent a Pseudorandom function and the Lth hybrid a truly random function *)
local clone import PROM.FullRO as G0_RO with
  type in_t <- unit,
  type out_t <- group,
  type d_in_t <- unit,
  type d_out_t <- bool,
  op dout _ <- sample.

local module G0 = RO.
local module LG0 = FullEager.LRO.

local module Hj (G0 : G0_RO.RO) = {
  (* Our hybrid parameter *)
  var j   : int

  var gis : group list (* In the general case this will be a list of group elements of size l - j *)

  var yqs : (bool list, set) fmap (* Store any previous query's result *)

  module O = {
    proc f(x) = {
      var xs <- ofbits x;
      var  p <- take j xs;
      var  s <- drop j xs;
      var gq;
      var yq;
      var r <- witness;
      var g;

      (* We have a special case for the 0th hybrid *)
      if (j = 0) {
        g <@ G0.get();
        yq <- act g x0;
      } else {
        if (p \notin yqs) {
          gq <$ sample; (* FIXME: When the PRF theory is updated this line should be moved before the if *)
          yqs.[p] <- act gq x0;
        }
        yq <- oget (yqs.[p]);
      }
      r <- compute_action gis s yq;
      
      return r;
    }
  }

  proc run(J : int) : bool = {
    var b;

      j <- J;
    G0.init();
    G0.sample();
    gis <$ dlist sample (l - j);
    yqs <- empty;

      b <@ D(O).distinguish();
    return b;
  }
}.

local clone import Program with
  type t <- group,
  op d <- sample.

local equiv PRF_Hybrid0:
  IND(PRF, D).main ~ Hj(G0).run:
    ={glob D} /\ J{2} = 0
    ==> ={res}.
proof.
proc=> /=.
call (:    Hj.j{2} = 0
        /\ size Hj.gis{2} = l - Hj.j{2}
        /\ () \in G0.m{2}
        /\ PRF.k{1} = mkkey ((oget G0.m.[()]) :: Hj.gis){2}).
+ proc; inline *.
  rcondt {2} 5; 1:by auto.
  rcondf {2} 7; 1:by auto.
  auto=> /> &2 gis_size tt_in g gin @/F /=.
  rewrite drop0 getE ofkeyK /= 1:gis_size 1:addzC //.
  smt(gt0_l).
inline *; sp; auto; conseq />.
rcondt {2} 2; first by auto=> />; rewrite mem_empty.
swap {2} 3 -2.
wp.
transitivity {2}
    {Hj.gis <@ SampleCons.sample(l + 1);}
    (true ==> PRF.k{1} = mkkey Hj.gis{2})
    (x0{2} = tt /\ Hj.j{2} = 0 ==> x0{2} = tt /\ size Hj.gis{2} = l /\ Hj.gis{1} = (r :: Hj.gis){2})=> //.
+ move=> &1 &m &2 ->; case: (x0{2})=> />.
  by rewrite domE get_set_sameE.
+ transitivity {2}
    {Hj.gis <@ Sample.sample(l + 1);}
    (true ==> PRF.k{1} = mkkey Hj.gis{2})
    (true ==> ={Hj.gis})=> //; first last.
  + by call Sample_SampleCons_eq; auto=> /=; smt(gt0_l).
  inline *; wp; rnd ofkey mkkey; auto=> />.
  split.
  + move=> gis gis_in; rewrite ofkeyK //.
    by move: gis_in; apply supp_dlist_size; smt(gt0_l).
  move=> a; split.
  + move=> gis gis_in.
    rewrite (dmap1E_can _ mkkey ofkey).
    + exact mkkeyK.
    + by move=> r /(a r); rewrite eq_sym.
    by rewrite {1}(a gis gis_in).
  move=> b k kin; rewrite mkkeyK /= -(size_key k).
  by apply: dlist_fu=> x _; exact DG.dunifin_fu.
inline *; auto=> /> gis + _ _.
by apply: supp_dlist_size; smt(gt0_l).
qed.

local lemma PRF_Hybrid0_pr &m:
    Pr[IND(PRF, D).main() @ &m: res]
  = Pr[Hj(G0).run(0) @ &m: res].
proof. by byequiv PRF_Hybrid0. qed.

local equiv PRF_HybridL:
  IND(RF, D).main ~ Hj(G0).run:
    ={glob D} /\ J{2} = l ==> ={res}.
proof.
proc=> /=; inline *.
call (:    Hj.j{2} = l
        /\ (forall (p : bool list), p \in Hj.yqs{2} => size p = l)
        /\ (forall (x : D), RF.m.[x]{1} = Hj.yqs.[ofbits x]{2})).
+ proc; auto.
  rcondf {2} 5; 1:by auto; smt(gt0_l).
  inline *.
  sp; if=> /=.
  + auto=> /> &1 &2 size_p val_eq.
    by rewrite !domE !(val_eq x{2}) -!domE -(size_bits x{2}) take_size.
  + wp; rnd (fun x => extract x0 x) (fun g => act g x0).
    auto=> /> &1 &2 size_p val_eq nin.
    split=> [g _ | _]; first exact extractUniq.
    split=> [g _ | _ r _]; first exact sample_dR_iso.
    rewrite extractP !get_set_sameE /=.
    rewrite drop_oversize 2:take_oversize 1,2:size_bits //=.
    split; first case (Hj.gis{2})=> />.
    split.
    + move=> p; rewrite domE get_setE.
      case (p = ofbits x{2})=> />.
      + exact: size_bits.
      by rewrite -domE=> _; exact: size_p.
    move=> x'; rewrite !get_setE; case (x' = x{2})=> />.
    case (ofbits x' = ofbits x{2}).
    + by move=> /ofbits_inj.
    by move: (val_eq x')=> ->.
  auto=> &1 &2 /> size_p eqv xin.
  rewrite -(size_bits x{2}) drop_size take_size eqv.
  by case (Hj.gis{2})=> />.
rcondt {2} 6.
+ by auto=> />; rewrite mem_empty.
by auto=> />; smt(emptyE).
qed.

local lemma PRF_HybridL_pr &m:
    Pr[IND(RF, D).main() @ &m: res]
  = Pr[Hj(G0).run(l) @ &m: res].
proof. by byequiv PRF_HybridL. qed.

(* Simple reduction statement for the case of l = 1 *)
local lemma Hybrid_PRF_Reduction &m :
     `|Pr[IND(PRF, D).main() @ &m: res] - Pr[IND(RF, D).main() @ &m: res]|
   = `|Pr[Hj(G0).run(0) @ &m: res] - Pr[Hj(G0).run(l) @ &m: res]|.
proof. by rewrite (PRF_HybridL_pr &m) (PRF_Hybrid0_pr &m). qed.

(* -------------------------------------------------------- *)
(* Proving the hybrid reduction of lemma 4.21/ theorem 4.19 *)
local clone import PROM.FullRO as XRO_t with
  type in_t    <- bool list,
  type out_t   <- R,
  type d_in_t  <- int,
  type d_out_t <- bool,
    op dout _  <- dR. (* Might need to change this, who knows? *)

local module X  = RO.
local module LX = FullEager.LRO.

local clone import PROM.FullRO as YRO_t with
  type in_t    <- bool list,
  type out_t   <- R,
  type d_in_t  <- int,
  type d_out_t <- bool,
    op dout _  <- dR. (* Might need to change this, who knows? *)

local module Y  = RO.
local module LY = FullEager.LRO.

local clone import PROM.FullRO as XYRO_t with
  type in_t    <- bool list,
  type out_t   <- R * R,
  type d_in_t  <- int,
  type d_out_t <- bool,
    op dout _  <- dR `*` dR.

local module XY  = RO.
local module LXY = FullEager.LRO.

local module XY_Real = {
    var m : (bool list, R * R) fmap
    var g : group

    proc init() = {
      g <$ sample;
      m <- empty;
    }

    proc get(x) = {
      var xq, yq : set;

      if (x \notin m) {
        xq <$ dR;
        yq <- act g xq;
        m.[x] <- (xq, yq);
      }
      return oget m.[x];
    }

    proc set(x, y) = {
      m.[x] <- y;
    }

    proc rem(x) = {
      m <- SmtMap.rem m x;
    }

    proc sample(x) = {
      get(x);
    }

    proc restrK() = {
      return m;
    }
}.

local module DecompWP (O : WP) = {
  var m : (bool list, R * R) fmap

  proc init() = {
         O.init();
    m <- empty;
  }

  proc get(x) = {
    var xy;

    if (x \notin m) {
         xy <@ O.query();
      m.[x] <- xy;
    }
    return oget m.[x];
  }

  proc set(x, y) = {
    m.[x] <- y;
  }

  proc rem(x) = {
    m <- SmtMap.rem m x;
  }

  proc sample(x) = {
    get(x);
  }

  proc restrK() = {
    return m;
  }
}.

local module R (D : RO_Distinguisher) (O : WP_Oracles) = {
  module O' = {
    proc init = WP_Real.init
    proc query = O.query
  }

  proc distinguish(J : int) = {
    var b;

         DecompWP(O').init();
    b <@ D(DecompWP(O')).distinguish(J);
    return b;
  }
}.

local clone import WPRF as WeakPRF.

require (*--*) DProd.
clone DProd.ProdSampling with
  type t1 <- set,
  type t2 <- set.

local equiv XY_WP_Ideal (D <: RO_Distinguisher { XY, WF, WS, WP_Real, DecompWP }):
  MainD(D, XY).distinguish ~ WP_IND(WS, R(D)).main:
    ={glob D, arg} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={m}(XY, DecompWP))=> //.
+ by proc; inline *; auto.
+ proc; if {2}; last by auto.
  rcondt {1} 2; first by auto.
  inline *; auto=> />.
  conseq (: r{1} = (xq, yq){2})=> //.
  transitivity {1}
        { r <@ ProdSampling.S.sample(dR, dR); }
        (true ==> ={r})
        (true ==> r{1} = (xq, yq){2})=> //.
  + by inline {2} 1; auto.
  transitivity {2}
        { (xq, yq) <@ ProdSampling.S.sample2(dR, dR); }
        ( true ==> r{1} = (xq, yq){2})
        (true ==> ={xq, yq})=> //.
  + by call ProdSampling.sample_sample2; auto=> /> [].
  by inline {1} 1; auto.
+ by sim.
+ by sim.
+ proc; inline *; sp; if {2}; last by auto.
  rcondt {1} 2; first by auto.
  inline *; auto=> />.
  conseq (: r{1} = (xq, yq){2})=> //.
  transitivity {1}
        { r <@ ProdSampling.S.sample(dR, dR); }
        (true ==> ={r})
        (true ==> r{1} = (xq, yq){2})=> //.
  + by inline {2} 1; auto.
  transitivity {2}
        { (xq, yq) <@ ProdSampling.S.sample2(dR, dR); }
        ( true ==> r{1} = (xq, yq){2})
        (true ==> ={xq, yq})=> //.
   + by call ProdSampling.sample_sample2; auto=> /> [].
   by inline {1} 1; auto.
by inline *; auto.
qed.

local equiv XY_WP_Real ( D <: RO_Distinguisher { XY_Real, WP_Real, DecompWP }):
  MainD(D, XY_Real).distinguish ~ WP_IND(WP_Real, R(D)).main:
    ={glob D, arg} ==> ={res}.
proof.
proc; inline *; wp.
call (: ={m}(XY_Real, DecompWP) /\ ={g}(XY_Real, WP_Real))=> //.
+ by proc; inline *; auto.
+ by proc; if=> //; inline *; auto.
+ by sim.
+ by sim.
+ by proc; inline *; sp; if=> //; inline *; auto.
by inline *; auto.
qed.

(** The hybrid—distinguishes random {(xq,yq)} from pseudorandom {(xq,yq)}
    We index the family with query prefixes because we don't really
    care about what the index is: we;; run a hybrid over it anyway
**)
local module Bj (XYs : RO) = {
  var j   : int

  var gis : group list

  module O = {
    proc f(x) = {
      var xq, yq;
      var xs <- ofbits x;
      var  p <- take j xs;
      var  b <- nth witness xs j;
      var  s <- drop (j + 1) xs;
      var  r <- witness;

      (xq, yq) <@ XYs.get(p);
      r <- compute_action gis s (if b then yq else xq);
      return r;
    }
  }

  proc distinguish(J) = {
    var b;
           XYs.init();
      j <- J;
    gis <$ dlist sample (l - j - 1); (* This should only sample for indices [j+2, l] *)
      b <@ D(O).distinguish();
    return b;
  }
}.

(** In this version of the hybrids, we only sample the value that's needed **)
local module B' (Xs : XRO_t.RO) (Ys : YRO_t.RO) = {
  var j   : int

  var gis : group list

  module O = {
    proc f(x) = {
      var xs <- ofbits x;
      var  p <- take j xs;
      var  b <- nth witness xs j;
      var  s <- drop (j + 1) xs;
      var  r <- witness;

      if (b) {
             Xs.sample(p);
        r <@ Ys.get(p);
      } else {
        r <@ Xs.get(p);
             Ys.sample(p);
      }
      r <- compute_action gis s r;
      
      return r;
    }
  }

  proc distinguish(J) = {
    var b;
           Xs.init();
           Ys.init();
      j <- J;
    gis <$ dlist sample (l - j - 1); (* This should only sample for indices [j+2, l] *)
      b <@ D(O).distinguish();
    return b;
  }
}.

local clone import DProd.ProdSampling as ProdR with
  type t1 <- R,
  type t2 <- R.

(** Simple wrappers to consider distinguishers against one or the other RO **)
local module B'_X (Y : YRO_t.RO) (X : XRO_t.RO) = {
  proc distinguish(J : int) = {
    var b;

    b <@ B'(X, Y).distinguish(J);
    return b;
  }
}.

local module B'_Y (X : XRO_t.RO) (Y : YRO_t.RO) = {
  proc distinguish(J : int) = {
    var b;

    b <@ B'(X, Y).distinguish(J);
    return b;
  }
}.

local equiv split_XY:
    Bj(XY).distinguish ~ B'(LX, LY).distinguish:
          ={glob D, arg}
      ==> ={glob D, res}.
proof.
transitivity
  B'_X(LY, X).distinguish
  (={glob D, arg} ==> ={glob D, res})
  (={glob D, glob X, glob Y, arg} ==> ={glob D, res})=> // [/#||]; last first.
+ transitivity
    B'_X(LY, LX).distinguish
    (={glob D, glob X, glob Y, glob B', arg} ==> ={glob D, res})
    (={glob D, glob X, glob Y, arg} ==> ={glob D, res})=> // [/#||].
  + conseq (XRO_t.FullEager.RO_LRO_D (B'_X(LY)) _)=> />.
    exact: (dR_ll witness).
  by proc; inline *; sim.
transitivity
  B'_Y(X, Y).distinguish
  (={glob D, arg} ==> ={glob D, res})
  (={glob D, glob X, glob Y, glob B', arg} ==> ={glob D, res})=> // [/#||]; last first.
+ transitivity
    B'_Y(X, LY).distinguish
    (={glob D, glob X, glob Y, glob B', arg} ==> ={glob D, res})
    (={glob D, glob X, glob Y, glob B', arg} ==> ={glob D, res})=> // [/#||].
  + conseq (YRO_t.FullEager.RO_LRO_D (B'_Y(X)) _)=> />.
    exact: (dR_ll witness).
  by proc; inline *; sim.
transitivity
  B'(X, Y).distinguish
  (={glob D, arg} ==> ={glob D, res})
  (={glob D, glob X, glob Y, arg} ==> ={glob D, res})=> // [/#||]; last first.
+ by proc; inline *; sim.
(** This should really have been kept as a separate lemma **)
proc.
call (:    ={j, gis}(Bj, B')
        /\ (forall p x y,
                  XY.m{1}.[p] = Some (x, y)
              <=> (X.m{2}.[p] = Some x /\ Y.m{2}.[p] = Some y))
        /\ (forall p, p \in X.m{2} <=> p \in Y.m{2})).
+ proc; sp.
  if {2}; inline *.
  + swap {2} 6 -3.
    exists * RO.m.[p]{1}; elim * => - [|[] xq yq].
    + rcondt {1} 3; 1:by auto=> /#.
      rcondt {2} 5.
      + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
        pose p := take Bj.j{m} (ofbits x{m}).
        rewrite !domE=> //= xy_p val_inv dom_inv.
        by move: (val_inv p) xy_p; case: (XY.m.[p]{m})=> /#.
      rcondt {2} 7.
      + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
        pose p := take Bj.j{m} (ofbits x{m}).
        rewrite !domE=> //= xy_p val_inv dom_inv.
        by move: (val_inv p) xy_p; case: (XY.m.[p]{m})=> /#.
      sp; auto; conseq (: r0{1} = (r1,r0){2}).
      + move=> /> &1 &2 /eq_sym.
        pose p := take Bj.j{2} (ofbits x{2}).
        move=> xy_p val_inv dom_inv _ r0 r1; rewrite !get_setE //=.
        smt(get_setE).
      transitivity {1}
        {r0 <@ ProdR.S.sample(dR, dR); }
        (true ==> ={r0})
        (true ==> r0{1} = (r1, r0){2})=> //.
      + by inline {2} 1; auto.
      transitivity {2}
        { (r1, r0) <@ ProdR.S.sample2(dR, dR); }
        (true ==> r0{1} = (r1, r0){2})
        (true ==> ={r0, r1})=> //.
      + by call ProdR.sample_sample2; auto=> /> [].
      by swap {2} 1 1; inline {1} 1; auto.
    rcondf {1} 3; 1:by auto=> /#.
    rcondf {2} 5.
    + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
      pose p := take Bj.j{m} (ofbits x{m}).
      rewrite !domE=> //= xy_p val_inv dom_inv.
      by move: (val_inv p xq yq); rewrite xy_p=> /> ->.
    rcondf {2} 6.
    + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
      pose p := take Bj.j{m} (ofbits x{m}).
      rewrite !domE=> //= xy_p val_inv dom_inv.
      by move: (val_inv p xq yq); rewrite xy_p=> /> _ ->.
    sp; auto; conseq (: r0{1} = (r1,r0){2}).
    + move=> /> &1 &2 /eq_sym.
      pose p := take B'.j{2} (ofbits x{2}).
      by move=> xy_p /(_ p xq yq) + _ _; rewrite xy_p=> /> _ ->.
    transitivity {1}
      {r0 <@ ProdR.S.sample(dR, dR); }
      (true ==> ={r0})
      (true ==> r0{1} = (r1, r0){2})=> //.
    + by inline {2} 1; auto.
    transitivity {2}
      { (r1, r0) <@ ProdR.S.sample2(dR, dR); }
      (true ==> r0{1} = (r1, r0){2})
      (true ==> ={r0, r1})=> //.
    + by call ProdR.sample_sample2; auto=> /> [].
    by swap {2} 1 1; inline {1} 1; auto.
  swap {2} 7 -4.
  exists * RO.m.[p]{1}; elim * => - [|[] xq yq].
  + rcondt {1} 3; 1:by auto=> /#.
    rcondt {2} 4.
    + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
      pose p := take Bj.j{m} (ofbits x{m}).
      rewrite !domE=> //= xy_p val_inv dom_inv.
      by move: (val_inv p) xy_p; case: (XY.m.[p]{m})=> /#.
    rcondt {2} 8.
    + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
      pose p := take Bj.j{m} (ofbits x{m}).
      rewrite !domE=> //= xy_p val_inv dom_inv.
      by move: (val_inv p) xy_p; case: (XY.m.[p]{m})=> /#.
    sp; auto; conseq (: r0{1} = (r0,r1){2}).
    + move=> /> &1 &2 /eq_sym.
      pose p := take B'.j{2} (ofbits x{2}).
      move=> xy_p val_inv dom_inv _ r0 r1; rewrite !get_setE //=.
      smt(get_setE).
    transitivity {1}
      {r0 <@ ProdR.S.sample(dR, dR); }
      (true ==> ={r0})
      (true ==> r0{1} = (r0, r1){2})=> //.
    + by inline {2} 1; auto.
    transitivity {2}
      { (r0, r1) <@ ProdR.S.sample2(dR, dR); }
      (true ==> r0{1} = (r0, r1){2})
      (true ==> ={r0, r1})=> //.
    + by call ProdR.sample_sample2; auto=> /> [].
    by inline {1} 1; auto.
  rcondf {1} 3; 1:by auto=> /#.
  rcondf {2} 4.
  + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
    pose p := take Bj.j{m} (ofbits x{m}).
    rewrite !domE=> //= xy_p val_inv dom_inv.
    by move: (val_inv p xq yq); rewrite xy_p=> /> ->.
  rcondf {2} 7.
  + auto=> /> &0 /eq_sym + + + _ _ _ _ _.
    pose p := take Bj.j{m} (ofbits x{m}).
    rewrite !domE=> //= xy_p val_inv dom_inv.
    by move: (val_inv p xq yq); rewrite xy_p=> /> _ ->.
  sp; auto; conseq (: r0{1} = (r0,r1){2}).
  + move=> /> &1 &2 /eq_sym.
    pose p := take B'.j{2} (ofbits x{2}).
    by move=> xy_p /(_ p xq yq) + _ _; rewrite xy_p=> /> ->.
  transitivity {1}
    {r0 <@ ProdR.S.sample(dR, dR); }
    (true ==> ={r0})
    (true ==> r0{1} = (r0, r1){2})=> //.
  + by inline {2} 1; auto.
  transitivity {2}
    { (r0, r1) <@ ProdR.S.sample2(dR, dR); }
    (true ==> r0{1} = (r0, r1){2})
    (true ==> ={r0, r1})=> //.
  + by call ProdR.sample_sample2; auto=> /> [].
  by inline {1} 1; auto.
by inline *; auto=> /> _ _ _ p x y; rewrite !emptyE.
qed.

local lemma HSj_BjI (j : int):
  0 <= j < l => equiv[Hj(G0).run ~ Bj(XY).distinguish:
    ={glob D} /\ J{1} = j + 1 /\ J{2} = j
    ==> ={res}].
proof.
move=> z_le_j_l_l.
transitivity
  B'(LX, LY).distinguish
  (={glob D} /\ J{1} = j + 1 /\ J{2} = j ==> ={res})
  (={glob D, arg} ==> ={res})=> // [/#||]; last first.
+ by symmetry; conseq split_XY.
proc; sp=> //=.
call (:    B'.j{2} = j /\ Hj.j{1} = j + 1
        /\ ={gis}(Hj, B')
        /\ size B'.gis{2} = l - B'.j{2} - 1
        /\ (forall p, p \in Hj.yqs{1} => size p = Hj.j{1})
        /\ (forall p, p \in Y.m{2} => size p = B'.j{2})
        /\ (forall p, p \in X.m{2} => size p = B'.j{2})
        /\ (forall p, Y.m.[p]{2} = Hj.yqs.[rcons p true]{1})
        /\ (forall p, X.m.[p]{2} = Hj.yqs.[rcons p false]{1})
        (** yqs[p' ++ [b]] = yq; _qs[p'] = (xq, gt * xq) **)).
+ proc; sp.
  rcondf {1} 1; 1:by auto=> /#.
  inline *.
  if {2}.
  + if {1}; [rcondt {2} 4|rcondf {2} 4].
    + auto=> /> &0 _ _ _ _ /(_ (take j (ofbits x{m}))).
      rewrite (take_nth witness).
      + by rewrite size_bits.
      move=> + + ->.
      by rewrite !domE=> /= <-.
    + auto; symmetry; rnd (extract x0) (fun g=> act g x0).
      auto=> /> &1 &2 B_gis_size domR_size domLy_size domLx_size valLRy valLRx xj x_notin_yqs.
      split=> [g _|_]; 1:exact: extractUniq.
      split=> [g _|_ r _]; 1:exact: sample_dR_iso.
      rewrite extractP !get_set_sameE /=.
      do! split=> p.
      + rewrite mem_set=> - [/domR_size | ->] //.
        by rewrite size_take [smt(size_bits)].
      + rewrite mem_set=> - [/domLy_size | ->] //.
        by rewrite size_take [smt(size_bits)].
      + rewrite (take_nth witness) 1:size_bits // xj !get_setE.
        case (p = take j (ofbits x{1}))=> //.
        case (rcons p true = rcons (take j (ofbits x{1})) true).
        + by rewrite -!cats1=> /catIs.
        move=> _ _.
        exact valLRy.
      rewrite (take_nth witness) 1:size_bits // xj !get_setE.
      case (rcons p false = rcons (take j (ofbits x{1})) true)=> />.
      + by move=> /rconsIs.
      move=> _.
      exact valLRx.
    + auto=> /> &1 Hj_gis_size domR_size domLy_size domLx_size valLRy valLRx xj + _ _.
      by rewrite (take_nth witness) 1:size_bits // xj !domE -valLRy.
    auto=> /> &1 &2 B_gis_size domR_size domLy_size domLx_size valLRy valLRx xj x_in_yqs _ _.
    congr; congr.
    by rewrite valLRy (take_nth witness) 1:size_bits // xj.
  if {1}; [rcondt {2} 3|rcondf {2} 3].
  + auto=> /> &0 _ _ _ _ _ /(_ (take j (ofbits x{m}))).
    rewrite (take_nth witness).
    + by rewrite size_bits.
    move=> + ->.
    by rewrite !domE=> /= <-.
  + auto; symmetry; rnd (extract x0) (fun g=> act g x0).
    auto=> /> &1 &2 B_gis_size domR_size domLy_size domLx_size valLRy valLRx xj x_notin_yqs.
    split=> [g _|_]; 1:exact: extractUniq.
    split=> [g _|_ r _]; 1:exact: sample_dR_iso.
    rewrite extractP !get_set_sameE /=.
    do! split=> p.
    + rewrite mem_set=> - [/domR_size | ->] //.
      by rewrite size_take [smt(size_bits)].
    + rewrite mem_set=> - [/domLx_size | ->] //.
      by rewrite size_take [smt(size_bits)].
    + rewrite (take_nth witness) 1:size_bits // xj !get_setE.
      case (rcons p true = rcons (take j (ofbits x{1})) false)=> />.
      + by move=> /rconsIs.
      move=> _.
      exact valLRy.
    rewrite (take_nth witness) 1:size_bits // xj !get_setE.
    case (p = take j (ofbits x{1}))=> //.
    case (rcons p false = rcons (take j (ofbits x{1})) false)=> //.
      + by rewrite -!cats1=> /catIs.
    move=> _ _.
    exact valLRx.
  + auto=> /> &1 Hj_gis_size domR_size domLy_size domLx_size valLRy valLRx xj + _ _.
    by rewrite (take_nth witness) 1:size_bits // xj !domE -valLRx.
  auto=> /> &1 &2 B_gis_size domR_size domLy_size domLx_size valLRy valLRx xj x_in_yqs _ _.
  congr; congr.
  by rewrite valLRx (take_nth witness) 1:size_bits // xj.
inline *.
sp; wp.
rnd.
auto=> /> g _.
split.
+ smt().
move=> _ gis gis_in.
split.
+ smt().
move=> _.
split; 1:apply (supp_dlist_size sample); smt(mem_empty emptyE).
qed.

local equiv H0_BjR:
   Hj(LG0).run ~ Bj(XY_Real).distinguish:
     ={glob D} /\ J{1} = 0 /\ J{2} = 0
     ==> ={res}.
proof.
proc=> //=.
inline *.
swap {2} 1 3.
call (:   ={j}(Hj, Bj) /\ Hj.j{1} = 0
      /\ (() \notin G0.m{1} <=> [] \notin XY_Real.m{2})
      /\ (Hj.gis{1} = (XY_Real.g :: Bj.gis){2})
      /\ size Bj.gis{2} = l - 1
      /\ (() \in G0.m{1} => act (oget G0.m.[()]{1}) x0 = (oget XY_Real.m.[[]]).`1{2})
      /\ (() \in G0.m{1} => act XY_Real.g{2} (act (oget G0.m.[()]{1}) x0) = (oget XY_Real.m.[[]]).`2{2})).
+ proc; inline *; sp.
  rcondt {1} 1; 1:by auto=> />.
  sp; if {2}=> />.
  + rcondt {1} 2; 1:auto=> /> &2.
    + case (x0{2})=> + _ _ _ + _ _.
      by rewrite take0=> ->.
    wp; symmetry; rnd (extract x0) (fun g=> act g x0).
    skip=> /> &1 &2 dom_eqv size_Bj_gis val_eq1 val_eq2 e_notin_m.
    split=> [g _|_]; 1:exact: extractUniq.
    split=> [g _|_ r _]; 1:exact: sample_dR_iso.
    case (x0{2}).
    rewrite !domE take0 !get_set_sameE !extractP drop0 /=.
    case {-1}(ofbits x{1}) (eq_refl (ofbits x{1}))=> />.
    + move=> /= /(congr1 size).
      rewrite size_bits /=.
      smt(gt0_l).
    move=> x1 l.
    rewrite drop0 !extractP.
    by case x1=> />.
  rcondf {1} 2; 1:auto=> /> &2.
  + case (x0{2})=> + _ _ _ + _ _.
    by rewrite take0=> ->.
  auto=> /> &1 &2 dom_eqv size_Bj_gis val_eq1 val_eq2.
  case (x0{1}).
  rewrite take0 drop0=> e_in g gin.
  split.
  + case {-1}(ofbits x{2}) (eq_refl (ofbits x{2}))=> />.
    + move=> /= /(congr1 size).
      rewrite size_bits /=.
      smt(gt0_l).
    move=> x1 l.
    rewrite drop0.
    rewrite -dom_eqv in e_in.
    case x1=> />.
    + by rewrite (val_eq2 e_in).
    by rewrite (val_eq1 e_in).
  by rewrite dom_eqv.
sp; wp.
conseq />.
transitivity {2}
  {Bj.gis <@ SampleCons.sample(l);}
  (Hj.j{1} = 0 ==> ={gis}(Hj, Bj))
  (Bj.j{2} = 0 ==> size Bj.gis{2} = l - 1 /\ Bj.gis{1} = (XY_Real.g :: Bj.gis){2})=> />; 1:smt(emptyE mem_empty); first last.
+ inline *; auto=> /> gis + _ _.
  apply supp_dlist_size.
  smt(gt0_l).
transitivity {2}
    {Bj.gis <@ Sample.sample(l);}
    (Hj.j{1} = 0 ==> ={gis}(Hj, Bj))
    (true ==> ={Bj.gis})=> //; last by call Sample_SampleCons_eq; auto=> />; smt(gt0_l).
by inline *; auto=> />.
qed.

local lemma Hj_BjR (j : int):
  0 < j < l =>
  equiv[Hj(LG0).run ~ Bj(XY_Real).distinguish:
    ={glob D} /\ J{1} = j /\ J{2} = j
    ==> ={res}].
proof.
move=> z_lt_j_lt_l.
proc=> //=.
inline *.
swap {2} 1 3.
call (:   ={j}(Hj, Bj) /\ Hj.j{1} = j
      /\ (Hj.gis{1} = (XY_Real.g :: Bj.gis){2})
      /\ size Bj.gis{2} = l - j - 1
      /\ (forall (p : bool list), p \in Hj.yqs{1} <=> p \in XY_Real.m{2})
      /\ (forall (p : bool list), p \in Hj.yqs{1} => oget Hj.yqs.[p]{1} = (oget XY_Real.m.[p]{2}).`1)
      /\ (forall (p : bool list), p \in Hj.yqs{1} => act XY_Real.g{2} (oget Hj.yqs.[p]{1}) = (oget XY_Real.m.[p]{2}).`2)).
+ proc; inline *; sp.
  rcondf {1} 1.
  + by auto=> /> &2 -> /#.
  sp; if=> //.
  + move=> &1 &2 /> _ eqv _.
    by rewrite (eqv _).
  + wp; symmetry; rnd (extract x0) (fun g=> act g x0).
    skip=> /> &1 &2 size_Bj_gis dom_eqv val_eq1 val_eq2 e_notin_m.
    split=> [g _|_]; 1:exact: extractUniq.
    split=> [g _|_ r _]; 1:exact: sample_dR_iso.
    rewrite !extractP get_set_sameE /=.
    split; first last.
    + split.
      + move=> p.
        rewrite !domE !get_setE.
        case (p = take j (ofbits x{1}))=> />.
        by rewrite -!domE (dom_eqv p).
      split.
      + move=> p.
        rewrite !domE !get_setE.
        case (p = take j (ofbits x{1}))=> />.
        rewrite -!domE=> _.
        exact val_eq1.
      move=> p.
      rewrite !domE !get_setE.
      case (p = take j (ofbits x{1}))=> />.
      rewrite -!domE=> _.
      exact val_eq2.
    case {-1}(ofbits x{1}) (eq_refl (ofbits x{1}))=> />.
    + move=> /= /(congr1 size).
      rewrite size_bits /=.
      smt(gt0_l).
    move=> x1 p'.
    case {-1}(j <= 0) (eq_refl (j <= 0))=> />; first smt.
    move=> _.
    case {-1}(j = 0) (eq_refl (j = 0))=> />; first smt.
    move=> _.
    case {-1}(j + 1 <= 0) (eq_refl (j + 1 <= 0))=> />; first smt.
    move=> _ use.
    rewrite get_set_sameE (drop_nth witness) /=.
    + move: use.
      move=> /(congr1 size).
      rewrite size_bits -cat1s size_cat /#.
    by case (nth witness p' (j - 1))=> />.
  auto=> /> &1 &2 size_Bj_gis dom_eqv val_eq1 val_eq2.
  case {-1}(ofbits x{2}) (eq_refl (ofbits x{2}))=> />.
  + move=> /= /(congr1 size).
    rewrite size_bits /=.
    smt(gt0_l).
  move=> x1 p'.
  case {-1}(j <= 0) (eq_refl (j <= 0))=> />; first smt.
  case {-1}(j = 0) (eq_refl (j = 0))=> />; first smt.
  case {-1}(j + 1 <= 0) (eq_refl (j + 1 <= 0))=> />; first smt.
  move=> _ _ _ use.
  rewrite (drop_nth witness) /=.
  + move: use.
    move=> /(congr1 size).
    rewrite size_bits -cat1s size_cat /#.
  case (nth witness p' (j - 1))=> /> _ p_in.
  + by rewrite val_eq2.
  by rewrite val_eq1.
sp; wp.
conseq />.
+ smt(mem_empty emptyE).
transitivity {2}
  {Bj.gis <@ SampleCons.sample(l - j);}
  (Hj.j{1} = j /\ J{1} = j ==> J{1} = j /\ ={gis}(Hj, Bj))
  (Bj.j{2} = j ==> size Bj.gis{2} = l - j - 1 /\ Bj.gis{1} = (XY_Real.g :: Bj.gis){2})=> />; 1:smt(emptyE mem_empty); first last.
+ inline *; auto=> /> gis + _ _.
  apply supp_dlist_size.
  smt(gt0_l).
transitivity {2}
    {Bj.gis <@ Sample.sample(l - j);}
    (Hj.j{1} = j ==> ={gis}(Hj, Bj))
    (true ==> ={Bj.gis})=> //; last by call Sample_SampleCons_eq; auto=> />; smt(gt0_l).
by inline *; auto=> />.
qed.

require (*--*) StdBigop.
(*---*) import StdBigop.Bigreal BRA.

lemma Security &m:
    `| Pr[IND(PRF, D).main() @ &m: res] - Pr[IND(RF, D).main() @ &m: res] |
    <=
    bigi predT
    (fun i => `| Pr[WP_IND(WP_Real, Red(D)).main(i) @ &m:res] - Pr[WP_IND(WP_Ideal, Red(D)).main(i) @ &m: res] |)
    0 (l-1).
rewrite Hybrid_PRF_Reduction.
have ->: Pr[Hj(G0).run(l) @ &m: res] = Pr[Bj(XY).distinguish(l - 1) @ &m: res].
byequiv (HSj_BjI (l-1) _)=> //.
+ smt(gt0_l).
end section PRF_Security.
