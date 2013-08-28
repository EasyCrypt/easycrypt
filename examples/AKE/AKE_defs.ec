require import Bool.
require import Int.
require import AWord.
require import FSet.
require import Map. 
require import List.
require import Distr.
require import Real.
require ISet.

(*{ Extensions to standard library *)

op def : 'a. (* types are inhabited, we define a polymorphic default value *)

(* Zero based intervals {0, .., k} of natural numbers *)
theory ZInter.
  const bound : int.
  axiom bound_geq_zero: bound >= 0.
  type t.
  op bounded(i : int) = 0 <= i /\ i <= bound.
  op abs : int -> t.
  op rep : t -> int.
  axiom rep_abs(i : int): bounded i => rep (abs i) = i.
  axiom abs_rep(x : t): abs (rep x) = x.
end ZInter.

op fdom(m : ('a,'b) map) : 'a set =
  ISet.Finite.toFSet (dom m).

op frng (m : ('a,'b) map) : 'b set =
  ISet.Finite.toFSet (rng m).

(*} *)

(*{ * Basic types and operators for protocol messages *)

type Sk.         (* static secret keys: a,b, .. *)
type Pk.         (* static public keys: A, B, .. *)

type Esk.        (* ephemeral secret key: x, y, *)
type Epk.        (* ephemeral public key: X, y *)

type Eexp.       (* ephemeral exponent: \tilde{x}=h(x,a) *)

type Agent = Pk. (* for now, we identify agents and public keys *)
type Sstring.    (* Input to hash H_2 to compute session key *)

const key_len : int.
clone import AWord as TKey with op length <- key_len.
type Key = TKey.word.

(*{ ** Define univ_type and sampling operators *)

op univ_Sk : Sk set.
axiom nosmt univ_Sk_all_mem : forall (x : Sk), mem x univ_Sk.
op sample_Sk = Duni.duni univ_Sk.

op univ_Esk : Esk set.
axiom nosmt univ_Esk_all_mem : forall (x : Esk), mem x univ_Esk.
op sample_Esk = Duni.duni univ_Esk.

op univ_Eexp : Eexp set.
axiom nosmt univ_Eexp_all_mem : forall (x : Eexp), mem x univ_Eexp.
op sample_Eexp = Duni.duni univ_Eexp.

op univ_Key : Key set.
axiom nosmt univ_Key_all_mem : forall (x : Key), mem x univ_Key.
op sample_Key = Dword.dword.
(*} *)

op gen_pk : Sk -> Pk.
op gen_epk : Eexp -> Epk.
op gen_sstring_init : Eexp -> Sk -> Pk -> Epk -> Sstring.
op gen_sstring_resp : Eexp -> Sk -> Pk -> Epk -> Sstring.

(*} *)

(*{ * Basic types and operators for protocol sessions *)

(* type role = Init | Resp *)
type Role = bool.

const init : bool = true.
const resp : bool = false.

op gen_sstring (x' : Eexp, a : Sk, B : Pk, Y : Epk, r : Role) = 
  if r then gen_sstring_init x' a B Y else gen_sstring_resp x' a B Y.

(* Session-id for completed session *)
type Sid = (Agent * Agent * Epk * Epk * Role).

(*{ ** Accessors for Sid *)
op sid_actor(sid : Sid) = let (A,B,X,Y,r) = sid in A.
op sid_peer(sid : Sid) = let (A,B,X,Y,r) = sid in B.
op sid_sent(sid : Sid) = let (A,B,X,Y,r) = sid in X.
op sid_rcvd(sid : Sid) = let (A,B,X,Y,r) = sid in Y.
op sid_role(sid : Sid) = let (A,B,X,Y,r) = sid in r.
(*} *)

(* Session-id for incomplete session *)
type Psid = (Agent * Agent * Epk * Role).

(*{ ** Accessors for PSid *)
op psid_actor(psid : Psid) = let (A,B,X,r) = psid in A.
op psid_peer(psid : Psid) = let (A,B,X,r) = psid in B.
op psid_sent(psid : Psid) = let (A,B,X,r) = psid in X.
op psid_role(psid : Psid) = let (A,B,X,r) = psid in r.
(*} *)

op psid_of_sid(sid : Sid) =  let (A,B,X,Y,r) = sid in (A,B,X,r).

(* (Private) data of incomplete session *)
type Sdata = (Agent * Agent * Esk * Eexp * Role).

(*{ ** Accessors for PSid *)
op sd_actor(sdata : Sdata) = let (A,B,x,x',r) = sdata in A.
op sd_peer(sdata : Sdata)  = let (A,B,x,x',r) = sdata in B.
op sd_eexp(sdata : Sdata)  = let (A,B,x,x',r) = sdata in x'.
op sd_esk(sdata : Sdata)   = let (A,B,x,x',r) = sdata in x.
op sd_role(sdata : Sdata)  = let (A,B,x,x',r) = sdata in r.
(*} *)

op psid_of_sdata(sdata : Sdata) =
  let (A,B,x,x',r) = sdata in (A,B,gen_epk(x'),r).

op sid_of_sdata(sdata : Sdata, Y : Epk) =
  let (A,B,x,x',r) = sdata in (A,B,gen_epk(x'),Y,r).

(* Strong partnering property *)
axiom nosmt strong_partnering(x', y' : Eexp) (a, b : Sk) (A, B : Pk) (X, Y : Epk) (r1, r2 : Role):
    gen_sstring x' a B Y r1 = gen_sstring y' b A X r2 <=>
    ((a = b /\ x' = y' /\ A = B /\ X = Y /\ r1 = r2) \/
    (A = gen_pk(a) /\ B = gen_pk(b) /\ X = gen_epk(x') /\ Y = gen_epk(y') /\ r1 <> r2)).

(*} *)

(*{ * Query events, matching, and freshness *)

(* type Event = StaticRev of Agent 
              | EphemeralRev of PSid 
              | SessionRev of Sid 
              | Start of psid
              | Accept of Sid *)
type Event.

op StaticRev : Agent -> Event.
op EphemeralRev : Psid -> Event.
op SessionRev : Sid -> Event.
op Start : Psid -> Event.
op Accept : Sid -> Event.

(*{ ** Axioms for inductive data type Event *)
axiom Event_no_junk(Ev : Event):
     (exists (A : Agent), Ev = StaticRev(A))
  \/ (exists (s : Psid), Ev = EphemeralRev(s))
  \/ (exists (s : Sid), Ev = SessionRev(s))
  \/ (exists (s : Sid), Ev = Accept(s))
  \/ (exists (s : Psid), Ev = Start(s)).

axiom Event_free1(A : Agent) (s : Psid):  StaticRev(A)     <> EphemeralRev(s).
axiom Event_free2(A : Agent) (s : Sid):   StaticRev(A)     <> SessionRev(s).
axiom Event_free3(A : Agent) (s : Psid):  StaticRev(A)     <> Start(s).
axiom Event_free4(A : Agent) (s : Sid):   StaticRev(A)     <> Accept(s).
axiom Event_free5(s1 : Psid) (s2 : Sid):  EphemeralRev(s1) <> SessionRev(s2).
axiom Event_free6(s1 : Psid) (s2 : Psid): EphemeralRev(s1) <> Start(s2).
axiom Event_free7(s1 : Psid) (s2 : Sid):  EphemeralRev(s1) <> Accept(s2).
axiom Event_free8(s1 : Sid) (s2 : Psid):  SessionRev(s1)   <> Start(s2).
axiom Event_free9(s1, s2 : Sid):          SessionRev(s1)   <> Accept(s2).
axiom Event_free10(s1 : Psid) (s2 : Sid): Start(s1)        <> Accept(s2).

axiom StaticRev_inj(A, B : Agent): StaticRev(A) = StaticRev(B) => A = B.

axiom EphemeralRev_inj(s1, s2 : Psid): EphemeralRev(s1) = EphemeralRev(s2) => s1 = s2.

axiom SessionRev_inj(s1, s2 : Sid): SessionRev(s1) = SessionRev(s2) => s1 = s2.

axiom Start_inj(s1, s2 : Psid): Start(s1) = Start(s2) => s1 = s2.

axiom Accept_inj(s1, s2 : Sid): Accept(s1) = Accept(s2) => s1 = s2.
(*} *)

(* Returns complete matching session of given session *)
op cmatching(t : Sid) = let (A,B,X,Y,r) = t in (B,A,Y,X,!r).

(* The (completed) session t is fresh if *)
pred fresh(t : Sid,  evs : Event list) =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
  let pt = psid_of_sid t in
  let s = cmatching t in
  let ps = psid_of_sid s in
  (* 1. t's session key has not been revealed, and *)
     !(List.mem (SessionRev t) evs)
  (* 2. t's ephemeral secret key and static secret key have not been both revealed, and *)
  /\ !(List.mem (EphemeralRev pt) evs /\ List.mem (StaticRev t_actor) evs)
  (* 3. the session key of a matching session of t has not been revealed, and *)
  /\ !(List.mem (SessionRev s) evs)
  (* 4. If the static secret key of t's peer has been revealed, then *)
  /\ (   List.mem (StaticRev t_peer) evs
      =>
         (  ( (* a) there is a complete matching session, or *)
                 List.mem (Accept s) evs
              \/ (* an incomplete matching session *)
                 (   List.mem (Start ps) evs
                  /\ !(exists (z : Epk), List.mem (Accept (t_peer,t_actor,t_recvd,z,!r)) evs)))
          /\ (* b) there is no ephemeral key reveal for a (complete or incomplete) matching session *)
             !(List.mem (EphemeralRev ps) evs))).

(*{ ** Some properties of notfresh *)

(* The (completed) session t is fresh unless *)
pred notfresh(t : Sid,  evs : Event list)  =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
  let pt = psid_of_sid t in
  let s = cmatching t in
  let ps = psid_of_sid s in
  (* 1. t's session key has been revealed, or *)
     List.mem (SessionRev t) evs
  (* 2. t's ephemeral secret and static keys have been revealed, or *)
  \/ (List.mem (EphemeralRev pt) evs /\ List.mem (StaticRev t_actor) evs)
  (* 3. the session key of a matching session of t has been revealed, or *)
  \/ List.mem (SessionRev s) evs
  (* 4. the static key of t's peer has been revealed, and *)
  \/ (   List.mem (StaticRev t_peer) evs
      /\ (   (* a) there is no complete matching session, and *)
             (    !List.mem (Accept s) evs
              (* no incomplete matching session *)
              /\  (   !List.mem (Start ps) evs
                   \/ (exists (z : Epk), List.mem (Accept (t_peer,t_actor,t_recvd,z,!r)) evs)))
          \/ (* b) there is an ephemeral reveal for a (complete or incomplete) matching session *)
             List.mem (EphemeralRev ps) evs)).

lemma nosmt not_or:
  forall P Q, (! (P \/ Q)) = (! P /\ ! Q) by [].

lemma nosmt not_and:
  forall P Q, (! (P /\ Q)) = (! P \/ ! Q) by [].

lemma nosmt not_not : 
  forall (P : bool), ! ! P = P by [].


lemma not_fresh_imp_notfresh(t : Sid) (evs : Event list):
  !(fresh t evs) => (notfresh t evs).
proof.
 rewrite /fresh /notfresh.
 by elim /tuple5_ind t => /=;progress; generalize H; rewrite !not_and;smt.
save.

lemma nosmt not_def(P): (P => false) => !P by [].

lemma notfresh_imp_notfresh(t : Sid) (evs : Event list):
  (notfresh t evs) => !(fresh t evs).
proof.
 rewrite /fresh /notfresh.
 by elim /tuple5_ind t => /=;progress; generalize H; rewrite !not_and;smt.
save.

lemma not_fresh_notfresh(t : Sid) (evs : Event list):
  (notfresh t evs) => !(fresh t evs) by [].

lemma nosmt absurd : forall P Q, !P => P => Q by [].

lemma nosmt diff_cons(x y : 'a) (xs : 'a list):
  ! mem x xs =>
  mem x (y::xs) => y = x by [].

lemma notfresh_fresh_ev(t : Sid) (evs : Event list) (e : Event):
  notfresh t evs =>
  fresh t (e::evs) => (mem (StaticRev (sid_peer t)) evs /\
  (e = Accept (cmatching t) \/ 
  e = Start (psid_of_sid (cmatching t)))).
proof.
  elim/tuple5_ind t => A B X Y r.
  intros=> teq hnfresh hfresh. clear teq.
  generalize hnfresh. rewrite /notfresh /= => hnfresh.
  generalize hfresh; rewrite /fresh /= => [H][H0][H1] H2.
  elim hnfresh => {hnfresh}; first smt.
  intros=> hnfresh. elim hnfresh => {hnfresh}. smt.
  intros=> hnfresh. elim hnfresh => {hnfresh}. smt.
  intros=> h.
  elim h => {h} h1 h2.
  cut G:= H2 _. smt.
  elim h2 => {h2} h2; last smt.
  elim h2 => {h2} Hacc Hst.
  elim Hst => {Hst} Hst.
  elim G => hno_match hnoeph.
  elim hno_match => no_accept.
  generalize no_accept; rewrite mem_cons => [|]; smt.
  elim  no_accept => {no_accept} no_start no_other_accept.
  generalize no_start; rewrite mem_cons => [|]; smt.
  elim G => hno_match hnoeph.
  elim hno_match => no_accept.
  generalize no_accept; rewrite mem_cons => [|]; smt.
  elim  no_accept => {no_accept} no_start no_other_accept.
  elim Hst => Z hZ.
  cut _ : (exists (z : Epk),
                      mem (Accept (B, A, Y, z, ! r)) (e :: evs)); last by smt.
  by exists Z; rewrite mem_cons; right; assumption.
qed.

lemma nosmt notfresh_fresh(t : Sid) (evs : Event list) (e : Event):
  e <> Accept (cmatching t) => 
  e <> Start (psid_of_sid (cmatching t)) =>
  notfresh t evs =>
  notfresh t (e::evs).
proof.
 intros hneq1 hneq2 hnfresh.
 apply not_fresh_imp_notfresh.
 apply not_def => hfresh.
 by elim (notfresh_fresh_ev t evs e _ _) => // _ [|]; smt.
save.


(*{ *** Our definition is stronger than the original NAXOS definition *)

(* The (completed) session t is fresh if *)
pred fresh_eCK(t : Sid,  evs : Event list)  =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
  let pt = psid_of_sid t in
  let s = cmatching t in
  let ps = psid_of_sid s in
  (* 1. t's session key has not been revealed, and *)
     !(List.mem (SessionRev t) evs)
  (* 2. t's ephemeral secret key and static secret key have not been both revealed, and *)
  /\ !(List.mem (EphemeralRev pt) evs /\ List.mem (StaticRev t_actor) evs)
  (* 3. the session key of a matching session of t has not been revealed, and *)
  /\ !(List.mem (SessionRev s) evs)
  (* 4. If the static secret key of t's peer has been revealed, then *)
  /\ (   List.mem (StaticRev t_peer) evs
      =>
         (   (* a) there is a complete matching session, or *)
             List.mem (Accept s) evs
          /\ (* b) there is no ephemeral key reveal for a (complete or incomplete) matching session *)
             !(List.mem (EphemeralRev ps) evs))).

lemma nosmt fresh_eCK_imp_fresh(t : Sid) (evs : Event list):
  (fresh_eCK t evs) => (fresh t evs).
proof.
 rewrite /fresh_eCK /fresh;
 elim /tuple5_ind t => ? ? ? ? ? heq /=; progress => //; smt.
save.
(*} *)

(*} *)

(*} *)

(*{ * Basic types and definitions for initial AKE game *)

const qSession : int.
const qAgent :   int.
const qH1 :      int.
const qH2 :      int.

axiom qSession_pos: 0 < qSession.
axiom qAgent_pos:   0 < qAgent.
axiom qH1_pos:      0 < qH1.
axiom qH2_pos:      0 < qH2.

(* Session index: uniquely identifies sessions even in the presence of collisions *)
type Sidx. (* we use an abstract, finite type with qSession elements *)

op univ_Sidx : Sidx set.
axiom univ_Sidx_all_mem : forall (x : Sidx), mem x univ_Sidx.
op sample_Sidx = Duni.duni univ_Sidx.
axiom Sidx_card: card univ_Sidx = qSession.

lemma Sidx_iset_finite(s : Sidx ISet.set):
  ISet.Finite.finite s.
proof strict.
  rewrite /ISet.Finite.finite.
  exists (filter (lambda x, ISet.mem x s) univ_Sidx).
  rewrite /ISet.Finite.(==).
  intros x.
  rewrite mem_filter.
  smt.
qed.

module type AKE_Oracles = {
  fun h1_a(a : Sk, x : Esk) : Eexp option
  fun h2_a(sstring : Sstring) : Key option
  fun init1(i : Sidx, A : Agent, B : Agent) : Epk option
  fun init2(i : Sidx, Y : Epk) : unit
  fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option
  fun staticRev(A : Agent) : Sk option
  fun ephemeralRev(i : Sidx) : Esk option
  fun sessionRev(i : Sidx) : Key option
}.

module type Adv (O : AKE_Oracles) = {
  fun choose(s : Pk list) : Sidx
    {* O.h1_a O.h2_a O.init1 O.init2 O.resp O.staticRev O.ephemeralRev O.sessionRev}
  fun guess(k : Key option) : bool
}.

(*} *)