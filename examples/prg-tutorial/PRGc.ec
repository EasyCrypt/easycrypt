(* -------------------------------------------------------------------- *)
(** We start by setting up the proof environment, loading theories and
  * choosing options for the proof engine.                             **)
(** Know to work using EasyCrypt  with the following GIT hash           *
  *   ac9b6e7bc63468cbcc2367fefc1e7fb073a15642                          *)

(* Loading core datatype theories *)
require import AllCore List FSet SmtMap.
(* Loading algebraic theories *)
require import StdRing StdOrder StdBigop.
(*---*) import Ring.IntID RField IntOrder RealOrder Bigreal BRA.
(* Loading distribution theories *)
require import Distr DProd Mu_mem.

(* Loading support theory for the failure event lemma tactic *)
require (*--*) FelTactic.

(* Loading theories of security definitions *)
require (*--*) PRF PRG.

(** Ignore: This is now the preferred setup but is not yet the default **)
pragma -oldip. pragma +implicits.

(* -------------------------------------------------------------------- *)
(** We now set up the definitions                                      **)

(* A finite type of seeds and a lossless distribution *)
type seed.
op dseed: { seed distr | is_lossless dseed } as dseed_ll.

(* A finite type for internal states and its uniform distribution *)
type state.
op dstate: { state distr |    is_lossless dstate
                           /\ is_funiform dstate } as dstate_llfuni.

lemma dstate_ll  : is_lossless dstate by have []:= dstate_llfuni.

lemma dstate_funi: is_funiform dstate by have []:= dstate_llfuni.

lemma dstate_fu  : is_full dstate.
proof. by apply/funi_ll_full; [exact/dstate_funi|exact/dstate_ll]. qed.

(* Notation: pr_dstate is the probability mass of each element in state *)
op pr_dstate = mu dstate (pred1 witness).

(* A finite type for outputs and some uniform distribution *)
type output.
op dout: { output distr |    is_lossless dout
                          /\ is_uniform dout } as dout_lluf.

lemma dout_ll : is_lossless dout by have []:= dout_lluf.
lemma dout_uni: is_uniform dout by have []:= dout_lluf.

(* The PRF *)
op Fc: seed -> state -> state * output.

(* -------------------------------------------------------------------- *)
(* Our PRG construction *)
module SRG = {
  var s   : seed
  var st  : state

  proc init(): unit = {
    s  <$ dseed;
    st <$ dstate;
  }

  proc next(): output = {
    var r;
    (st,r) <- Fc s st;
    return r;
  }
}.

(* Some useful lemmas that will pop up all the time *)
lemma SRG_init_ll: islossless SRG.init.
proof. by proc; auto; rewrite dseed_ll dstate_ll. qed.

lemma SRG_next_ll: islossless SRG.next.
proof. by proc; auto. qed.

(* -------------------------------------------------------------------- *)
(* Defining the security of the PRF F by cloning *)
clone import PRF as PRFa with
  type D   <- state,
  type R   <- state * output,
  type K   <- seed,
  op   dK  <- dseed,
  op   F   <- Fc,
  op   uR  <- dstate `*` dout (* product distribution *)
(* We discharge all axioms *)
proof *.
(* Losslessness of the key distribution is losslessness of dseed *)
realize dK_ll by exact/dseed_ll.
(* Losslessness of the domain distribution follows from losslessness
   of the distributions on its components. *)
realize uR_uf.
by apply/dprod_uni; [exact/funi_uni/dstate_funi|exact/dout_uni].
qed.

lemma uR_ll: is_lossless (dstate `*` dout).
proof. by apply/dprod_ll; split; [exact/dstate_ll|exact/dout_ll]. qed.

module IND_PRF = PRFa.IND.
module PRFc = PRFa.PRFr.
module PRFi = PRFa.PRFi.
(* Adv^PRF_Fc(D) is defined as
     Pr[IND_PRF(PRFr,D).main() @ &m: res]
     - Pr[IND_PRF(PRFi,D).main() @ &m: res] *)

(* -------------------------------------------------------------------- *)
(* Defining the security of a PRG by cloning *)
clone import PRG as PRGa with
  type output <- output,
  op   dout   <- dout.

module IND_PRG = PRGa.IND.
module PRGi = PRGa.PRGi.
(* Adv^PRG_PRGc(D) is defined as
     Pr[IND_PRG(PRGc,D).main() @ &m: res]
     - Pr[IND_PRG(PRGi,D).main() @ &m: res] *)

(* -------------------------------------------------------------------- *)
(** The Proof starts here **)
(* We construct D_PRF from any PRG distinguisher D *)
module D_PRF (D:PRGa.Distinguisher,F:PRFA) = {
  var log:state list (* Not useful for the reduction, but for the proof. *)

  module PRGp = {
    proc init(): unit = {
      SRG.st <$ dstate;
      log    <- [];
    }

    proc next(): output = {
      var r;

      log        <- SRG.st::log;
      (SRG.st,r) <@ F.f(SRG.st);
      return r;
    } 
  }

  proc distinguish = IND_PRG(PRGp,D).main
}.

(* -------------------------------------------------------------------- *)
(** Rather than explicitly writing out the quantification over D,
  * we use a Section. This is not particularly useful here, but it
  * illustrates their effects nicely.                                  **)
section Fact1.
  (* Lemmas in this section are true forall PRG distinguisher D
     that do not share memory with SRG, PRFr, PRFi, or D_PRF. *)
  declare module D: PRGa.Distinguisher {SRG,PRFr,PRFi,D_PRF}.

  local lemma SRG_PRGp &m:
    Pr[IND_PRG(SRG,D).main() @ &m: res] = Pr[IND_PRF(PRFc,D_PRF(D)).main() @ &m: res].
  proof.
  byequiv (_: ={glob D} ==> ={res})=> //.
  proc; inline *; sim (: ={SRG.st} /\ SRG.s{1} = PRFc.k{2}): (={b}).
  by proc; inline *; sim.
  qed.

  (* Lemma Idealize_PRF:
       Adv^PRG_PRGc(D) = Adv^PRF_PRFc(D_PRF(D))
                       + Pr[IND^PRF_PRFi(D_PRF_D): res]
                       - Pr[IND^PRF_PRGi(D): res] *)
  lemma Idealize_PRF &m:
    Pr[IND_PRG(SRG,D).main() @ &m: res]
    - Pr[IND_PRG(PRGi,D).main() @ &m: res]
    = (Pr[IND_PRF(PRFc,D_PRF(D)).main() @ &m: res]
       - Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res])
      + Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res]
        - Pr[IND_PRG(PRGi,D).main() @ &m: res].
  proof. by rewrite (SRG_PRGp &m) /#. qed.
end section Fact1.

(** Observe that the quantification over D is introduced upon
  * closing the section, and that local lemmas have disappeared. **)
print lemma Idealize_PRF.

(* -------------------------------------------------------------------- *)
(** We use the following module to express a bad event that
  * corresponds (almost) exactly to the cases where the distinguisher
  * wins without breaking the PRF.                                     **)
module PRGil = {
  proc init(): unit = {
    SRG.st    <$ dstate;
    D_PRF.log <- [];
  }

  proc next(): output = {
    var r;

    D_PRF.log  <- SRG.st :: D_PRF.log;
    (SRG.st,r) <$ dstate `*` dout;
    return r;
  }
}.

lemma PRGil_init_ll: islossless PRGil.init.
proof. by proc; auto; rewrite dstate_ll. qed.

lemma PRGil_next_ll: islossless PRGil.next.
proof. by proc; auto; rewrite uR_ll. qed.

(* -------------------------------------------------------------------- *)
(* Resource accounting requires thin wrappers *)
(* for the PRG *)
module C_PRG(G:PRGa.RG) = {
  var c:int

  proc init(): unit = {
    c <- 0;
    G.init();
  }

  proc next(): output = {
    var r <- witness;

    r <@ G.next();
    c <- c + 1;
    return r;
  }
}.

module C_D_PRG(D:PRGa.Distinguisher,G:PRGa.RGA) = {
  module G' = {
    proc next(): output = {
      var r <- witness;

      r <@ G.next();
      C_PRG.c <- C_PRG.c + 1;
      return r;
    }
  }

  module D' = D(G')

  proc distinguish(): bool = {
    var b;
    C_PRG.c <- 0;
    b <@ D'.distinguish();
    return b;
  }
}.

equiv Count_PRG_equiv (G <: PRGa.RG {C_PRG}) (D <: PRGa.Distinguisher {G,C_PRG}):
  IND_PRG(C_PRG(G),D).main ~ IND_PRG(G,C_D_PRG(D)).main:
    ={glob D, glob G} ==> ={glob D, glob C_PRG(G), res}.
proof. by proc; inline *; swap{2} 2 -1; sim. qed.

lemma Count_PRG (G <: PRGa.RG {C_PRG}) (D <: PRGa.Distinguisher {G,C_PRG}) &m:
  Pr[IND_PRG(C_PRG(G),D).main() @ &m: res] = Pr[IND_PRG(G,C_D_PRG(D)).main() @ &m: res]
by byequiv (Count_PRG_equiv G D).

lemma Count_PRG_noop (G <: PRGa.RG {C_PRG}) (D <: PRGa.Distinguisher {G,C_PRG}) &m:
  Pr[IND_PRG(G,D).main() @ &m: res] = Pr[IND_PRG(C_PRG(G),D).main() @ &m: res].
proof.
byequiv=> //=; proc; inline *; sim (: ={glob G}): (={b}).
by proc *; inline *; sim.
qed.

(* and for the PRF *)
module C_PRF(F:PRFa.PRF) = {
  var c:int

  proc init(): unit = {
    c <- 0;
    F.init();
  }

  proc f(x:state): state * output = {
    var r <- witness;

    r <@ F.f(x);
    c <- c + 1;
    return r;
  }
}.

module C_D_PRF(D:PRFa.Distinguisher,F:PRFa.PRFA) = {
  module F' = {
    proc f(x:state): state * output = {
      var r <- witness;

      r <@ F.f(x);
      C_PRF.c <- C_PRF.c + 1;
      return r;
    }
  }

  module D' = D(F')

  proc distinguish(): bool = {
    var b;
    C_PRF.c <- 0;
    b <@ D'.distinguish();
    return b;
  }  
}.

equiv Count_PRF_equiv (F <: PRFa.PRF {C_PRF}) (D <: PRFa.Distinguisher {F,C_PRF}):
  IND_PRF(C_PRF(F),D).main ~ IND_PRF(F,C_D_PRF(D)).main:
    ={glob D, glob F} ==> ={glob D, glob C_PRF(F), res}.
proof. by proc; inline *; swap{2} 2 -1; sim. qed.

lemma Count_PRF (F <: PRFa.PRF {C_PRF}) (D <: PRFa.Distinguisher {F,C_PRF}) &m:
  Pr[IND_PRF(C_PRF(F),D).main() @ &m: res] = Pr[IND_PRF(F,C_D_PRF(D)).main() @ &m: res]
by byequiv (Count_PRF_equiv F D).

lemma Count_PRF_noop (F <: PRFa.PRF {C_PRF}) (D <: PRFa.Distinguisher {F,C_PRF}) &m:
  Pr[IND_PRF(F,D).main() @ &m: res] = Pr[IND_PRF(C_PRF(F),D).main() @ &m: res].
proof.
byequiv=> //=; proc; inline *; sim (: ={glob F}): (={b}).
by proc *; inline *; sim.
qed.

(* -------------------------------------------------------------------- *)
equiv Count_AdvQueries_PRF (F <: PRFa.PRF {SRG,D_PRF,C_PRF,C_PRG})
                           (D <: PRGa.Distinguisher {SRG,D_PRF,F,C_PRF,C_PRG}):
  IND_PRF(F,D_PRF(C_D_PRG(D))).main ~ IND_PRF(C_PRF(F),D_PRF(D)).main:
    ={glob F, glob D} ==> ={glob F, glob D, res} /\ ={c}(C_PRG,C_PRF).
proof.
proc; inline *; swap{1} 4 -3.
wp; call (_: ={glob F, SRG.st} /\ ={c}(C_PRG,C_PRF)).
  by proc; inline *; auto; call (_: true); auto.
by auto; call (_: true); auto.
qed.

(* -------------------------------------------------------------------- *)
(** We now prove Fact2:
  *   Pr[IND^PRF_PRFi(D^PRF_D): res] - Pr[IND^PRF_PRGi(D): res]
  *   <= Pr[IND^PRF_PRFi(D^PRF_D): !uniq D^PRF_D.log]                  **)
section Fact2.
  declare module D: PRGa.Distinguisher {SRG,PRFr,PRFi,D_PRF}.
  axiom D_distinguish_ll (G <: RGA {D}): islossless G.next => islossless D(G).distinguish.

  inductive inv (m : ('a,'b) fmap) (logP : 'a list) =
    | EqQueries of (dom m = mem logP).

  lemma invP (m : ('a,'b) fmap) (logP : 'a list):
    (forall r, r \in m <=> r \in logP) <=> inv m logP.
  proof. by split=> [/pred_ext /= /EqQueries|[] ->]. qed.

  local equiv PRFi_PRGil_upto: IND_PRF(PRFi,D_PRF(D)).main ~ IND_PRG(PRGil,D).main:
        ={glob D}
    ==>    (uniq D_PRF.log{1} <=> uniq D_PRF.log{2})
        /\ (uniq D_PRF.log{2} => ={res}).
  proof.
  proc; inline *; wp.
  call (_: !uniq D_PRF.log,
           uniq D_PRF.log{1} /\ ={SRG.st,D_PRF.log} /\ inv PRFi.m{1} D_PRF.log{1},
           !uniq D_PRF.log{1})=> /=.
    (* adversary is lossless *)
    by apply D_distinguish_ll.
    (* [F.f ~ F.f: I] when Bad does not hold *)
    proc=> //=; inline *; sp; if{1}=> //=.
      auto=> /> &1 &2 log uniq_log _ ih st_notin_m x x_in_stout st_notin_log.
      rewrite get_set_sameE /=.
      by case: ih=> ih; apply/invP=> s; rewrite mem_set ih orbC.
    auto=> /> &1 &2 log uniq_log _ ih st_in_m.
    rewrite uR_ll //= => str  _.
    by move: ih=> /invP <-.
    (* bad => second invariant is preserved *)
    move=> &2 Bad; proc; inline *; sp; if; auto=> [| /> &m log ->] />.
    by rewrite uR_ll //#.
    (* bad => lossless and bad right *)
    by move=> &1; proc; auto=> />; rewrite uR_ll /#.
  auto=> /> st _; split => [|/#].
  by rewrite -invP=> s; rewrite domE emptyE.
  qed.

  (* This one is not local as we use it to bound probabilities *)
  lemma PRFi_PRGil_bad &m:
    Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: !uniq D_PRF.log]
    = Pr[IND_PRG(PRGil,D).main() @ &m: !uniq D_PRF.log].
  proof. by byequiv PRFi_PRGil_upto=> // /#. qed.

  local lemma PRGi_PRGil &m:
    Pr[IND_PRG(PRGi,D).main() @ &m: res]
    = Pr[IND_PRG(PRGil,D).main() @ &m: res].
  proof.
  byequiv (_: ={glob D} ==> ={res})=> //=.
  sim (: true): (={res}).
    by proc; auto=> />; rewrite dstate_ll.
  bypr (res{1}) (res{2})=> //= &1 &2 o.
  have ->: Pr[PRGil.next() @ &2: res = o] = mu dout (pred1 o).
    byphoare (_: true ==> res = o)=> //=.
    proc; wp; rnd (fun (str : state * output)=> (pred1 o) str.`2); auto=> />.
    by rewrite (@dprodE predT (pred1 o)) dstate_ll.
  byphoare (_: true ==> res = o)=> //=.
  by proc; rnd; auto=> />; rewrite -(@pred1E o).
  qed.

  local lemma PRFi_PRGil &m:
    Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res] - Pr[IND_PRG(PRGil,D).main() @ &m: res]
    <= Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: !uniq D_PRF.log].
  proof.
  have: Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res]
        <= Pr[IND_PRG(PRGil,D).main() @ &m: res \/ !uniq D_PRF.log].
    by byequiv PRFi_PRGil_upto=> // /#.
  rewrite Pr [mu_or] -(PRFi_PRGil_bad &m).
  smt (mu_bounded).
  qed.

  lemma Fact2 &m:
    Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res] - Pr[IND_PRG(PRGi,D).main() @ &m: res]
    <= Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: !uniq D_PRF.log].
  proof. by rewrite (PRGi_PRGil &m) (PRFi_PRGil &m). qed.
end section Fact2.
  
(* This concludes the proof of Theorem 1. *)
lemma Theorem1 (D <: PRGa.Distinguisher {SRG,PRFc,PRFi,D_PRF}) &m:
  (forall (G <: RGA {D}), islossless G.next => islossless D(G).distinguish) =>
  Pr[IND_PRG(SRG,D).main() @ &m: res] - Pr[IND_PRG(PRGi,D).main() @ &m: res]
  <= (Pr[IND_PRF(PRFc,D_PRF(D)).main() @ &m: res]
      - Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res])
     + Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: !uniq D_PRF.log].
proof.
move=> D_distinguish_ll; rewrite (Idealize_PRF D &m).
by have /# := Fact2 D _ &m.
qed.

(*** We now bound resources and probabilities ***)
(* -------------------------------------------------------------------- *)
(** Lemma 2: Forall q \geq 0, and forall D that calls next at most q
             times, D_PRF(D) calls f at most q times. **)
lemma Lemma2 q (D <: PRGa.Distinguisher {SRG,PRFc,C_PRG,C_PRF,D_PRF}):
  (forall (G <: PRGa.RG {D,C_PRG}) &m,
    islossless G.init =>
    islossless G.next =>
    Pr[IND_PRG(C_PRG(G),D).main() @ &m: C_PRG.c <= q] = 1%r) =>
  forall &m, Pr[IND_PRF(C_PRF(PRFc),D_PRF(D)).main() @ &m: C_PRF.c <= q] = 1%r.
proof.
move=> D_bounded &m.
have ->: Pr[IND_PRF(C_PRF(PRFc),D_PRF(D)).main() @ &m: C_PRF.c <= q]
         = Pr[IND_PRG(C_PRG(SRG),D).main() @ &m: C_PRG.c <= q].
  byequiv (_: ={glob D} ==> C_PRF.c{1} = C_PRG.c{2})=> //.
  proc; inline *; wp.
  call (_: PRFr.k{1} = SRG.s{2} /\
           ={SRG.st} /\
           C_PRF.c{1} = C_PRG.c{2}).
    by proc; inline *; auto.
  by auto.
by rewrite (D_bounded SRG &m _ _) // ?(SRG_init_ll, SRG_next_ll).
qed.

(* -------------------------------------------------------------------- *)
(** Bounding Pr[IND_PRF(PRFi,D_PRF(D)): !unique D_PRF.logF] **)
op     qN : { int | 0 <= qN } as ge0_qN.

section Lemma1.
  declare module D : PRGa.Distinguisher {SRG,PRFc,PRFi,C_PRG,C_PRF,D_PRF}.

  axiom D_distinguish_ll (G <: PRGa.RGA {D}):
    islossless G.next => islossless D(G).distinguish.

  axiom D_bounded (G <: PRGa.RG {D,C_PRG}) &m:
    islossless G.init => islossless G.next =>
    Pr[IND_PRG(C_PRG(G),D).main() @ &m: C_PRG.c <= qN] = 1%r.

  (* We express the adversary assumption in Hoare form for use with
     conseq. This requires some gymnastics. *)
  lemma D_bounded_hoare (G <: RG {D,C_PRG}):
    islossless G.init =>
    islossless G.next =>
    hoare [IND_PRG(C_PRG(G),D).main: true ==> C_PRG.c <= qN].
  proof.
  move=> G_init_ll G_next_ll.
  hoare; bypr=> //= &m'; rewrite Pr [mu_not] (D_bounded G &m' G_init_ll G_next_ll).
  rewrite subr_eq0. byphoare (_: true ==> true)=> //.
  proc; call (D_distinguish_ll (C_PRG(G)) _).
    by proc; wp; call G_next_ll; auto.
  by inline *; call G_init_ll; auto.
  qed.

  lemma PRGsi_Bad_bound &m:
    Pr[IND_PRG(C_PRG(PRGil),D).main() @ &m: !uniq D_PRF.log] <= ((qN + 1) * qN)%r * pr_dstate / 2%r.
  proof.
  have ->: Pr[IND_PRG(C_PRG(PRGil),D).main() @ &m: !uniq D_PRF.log]
           = Pr[IND_PRG(C_PRG(PRGil),D).main() @ &m: !uniq D_PRF.log /\ C_PRG.c <= qN].
    byequiv (_: ={glob D} ==> ={D_PRF.log} /\ C_PRG.c{2} <= qN)=> //=.
    conseq (_: _ ==> ={D_PRF.log}) _ (D_bounded_hoare PRGil PRGil_init_ll PRGil_next_ll).
    by sim.
  (* We weaken the result a bit. This is not necessary but makes the
     proof much easier.
     EXERCISE (advanced): use eager to obtain qN * (qN - 1) in the bound. *)
  apply/(@ler_trans Pr[IND_PRG(C_PRG(PRGil),D).main() @ &m: !uniq (SRG.st::D_PRF.log) /\ C_PRG.c <= qN]).
    byequiv (_: ={glob D} ==> ={C_PRG.c,D_PRF.log})=> //=; first by sim.
    by move=> &1 &2 [] -> -> [] ->.
  (* We comment on the fel tactic. Its first parameter is the length
     of the initialization code. *)
  fel 1 (C_PRG.c)                       (* the query counter *)
        (fun i=> (i + 1)%r * pr_dstate) (* probability of bad first occurring during ith query *)
        qN                              (* the bound on the counter (after which we stop caring) *)
        (!uniq (SRG.st::D_PRF.log))     (* the bad event *)
        []                              (* condition(s) under which the oracle(s) do not respond *)
        (size D_PRF.log = C_PRG.c).     (* general unconditional invariants *)
    (* The resulting sum is less than the specified bound *)
    rewrite -mulr_suml mulrAC ler_wpmul2r 1:[smt (mu_bounded)].
    rewrite (@big_reindex _ _ ([-]%Int \o ((-) 1)) ((+) 1)) 1:[smt ml=0].
    rewrite predTofV (@eq_bigr _ _ CoreReal.from_int) 1:[smt ml=0].
    rewrite (@eq_map _ ((+) 1)) 2:-range_add /= 1:[smt ml=0].
    rewrite -(@add0r (bigi _ _ _ _)) -(@big1_eq predT (range 0 1)).
    rewrite (@eq_big_int _ _ _ CoreReal.from_int) 1:[smt ml=0] -big_cat -range_cat // 1:ler_addr 1:ge0_qN.
    by rewrite sumidE [smt (ge0_qN)].
    (* The bounded event implies that from the probability claim *)
    done.
    (* Initialization sets counter to 0, bad event to false, and
       establishes the invariant *)
    by inline *; auto.
    (* Probability of bad during cth iteration is bounded by "bound c" *)
    proc=> //=; inline *; wp.
    rnd (fun (str : state * output)=> mem D_PRF.log str.`1); auto=> /> &hr.
    rewrite (@dprodE (mem (SRG.st::D_PRF.log){hr}) predT) dout_ll /=.
    move=> ge0_szlog ltqN_szlog st_notin_log uniq_log.
    apply/(ler_trans ((size (SRG.st::D_PRF.log){hr})%r * pr_dstate)).
      by apply/mu_mem_le_size=> x _; rewrite (@dstate_funi x witness) ?dstate_fu.
    by apply/ler_wpmul2r; smt (mu_bounded).
    (* The unconditional invariant is preserved by oracle calls *)
    by move=> c; proc; inline *; auto=> /#.
  (* When condition does not hold, the counter value does not decrease
     and bad is not triggered *)
  done.
  qed.
end section Lemma1.

(** Forall PRG distinguisher D whose memory is disjoint from that of
    the interesting modules and such that:
      i)  D is lossless whenever G.next is; and
      ii) D makes at most qN calls to its next oracle,
    we have:
      Adv^PRG_SRG(D) <= Adv^PRF_PRFc(D_PRF(D)) + qN^2/|state|.        **)
lemma Security (D <: PRGa.Distinguisher {SRG,PRFc,PRFi,C_PRG,C_PRF,D_PRF}) &m:
  (forall (G <: PRGa.RGA {D}), islossless G.next => islossless D(G).distinguish) =>
  (forall (G <: PRGa.RG {D,C_PRG}) &m,
    islossless G.init => islossless G.next =>
    Pr[IND_PRG(C_PRG(G),D).main() @ &m: C_PRG.c <= qN] = 1%r) =>
  Pr[IND_PRG(SRG,D).main() @ &m: res] - Pr[IND_PRG(PRGi,D).main() @ &m: res]
  <= (Pr[IND_PRF(PRFc,D_PRF(D)).main() @ &m: res] - Pr[IND_PRF(PRFi,D_PRF(D)).main() @ &m: res])
     + ((qN + 1) * qN)%r * pr_dstate / 2%r.
proof.
(* The proof could be made a bit more elegant by introducing more
   abstraction for the query counting modules. We are not yet sure how
   to do it in the most general way, though, so we keep it like this
   for now. *)
move=> D_distinguish_ll D_bounded.
rewrite (Count_PRG_noop SRG D &m) (Count_PRG_noop PRGi D &m).
rewrite (Count_PRF_noop PRFc (D_PRF(D)) &m) (Count_PRF_noop PRFi (D_PRF(D)) &m).
have:= PRGsi_Bad_bound D _ _ &m=> //.
have C_D_PRG_ll: forall (G <: PRGa.RGA {C_D_PRG(D)}),
                   islossless G.next => islossless C_D_PRG(D,G).distinguish.
  move=> G G_next_ll; proc.
  call (_: true)=> //; first by proc; wp; call G_next_ll; wp.
  by auto.
have := Theorem1 (C_D_PRG(D)) &m _ => //.
rewrite -(Count_PRG SRG D &m) -(Count_PRG PRGi D &m).
have ->: Pr[IND_PRF(PRFc,D_PRF(C_D_PRG(D))).main() @ &m: res]
         = Pr[IND_PRF(C_PRF(PRFc),D_PRF(D)).main() @ &m: res].
  by byequiv (Count_AdvQueries_PRF PRFc D).
have ->: Pr[IND_PRF(PRFi,D_PRF(C_D_PRG(D))).main() @ &m: res]
         = Pr[IND_PRF(C_PRF(PRFi),D_PRF(D)).main() @ &m: res].
  by byequiv (Count_AdvQueries_PRF PRFi D).
rewrite (PRFi_PRGil_bad (C_D_PRG(D)) _ &m)=> //.
have ->: Pr[IND_PRG(PRGil,C_D_PRG(D)).main() @ &m: !uniq D_PRF.log]
         = Pr[IND_PRG(C_PRG(PRGil),D).main() @ &m: !uniq D_PRF.log].
  by rewrite eq_sym; byequiv (Count_PRG_equiv PRGil D).
smt ml=0.
qed.

print Security.
