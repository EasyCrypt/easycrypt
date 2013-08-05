require import Int.
require import Word.
require import FSet.
require import Map. 
require import List.
require import Distr.
require import Real.

theory AKE.

type Sk.  (* static secret keys: a,b, .. *)
type Pk.  (* static public keys: A, B, .. *)

type Esk. (* ephemeral secret key: x, y, *)
type Epk. (* ephemeral public key: X, y *)

const dEpk : Epk. (* default value for Epk type *)

type Eexp. (* ephemeral exponent: \tilde{x}=h(x,a) for NAXOS-style protocols *)

type Agent = Pk.     (* for now, we identify agents and public keys *)
type Session_string. (* Input to hash to compute session string *)

const k : int.

clone import Word as Key with op length <- k.

type Key = Key.word.

const sample_bstr_k : Key distr = Dword.dword.
const sample_sk : Sk distr.
const sample_esk : Esk distr.
const sample_eexp : Eexp distr.

axiom sample_sk_ll : Distr.weight sample_sk = 1%r.
axiom sample_esk_ll : Distr.weight sample_esk = 1%r.
axiom sample_eexp_ll : Distr.weight sample_eexp = 1%r.

lemma sample_bstr_k_mu_one : forall (P : Key cpred),
(forall (y : Key), (P y))  =>
mu sample_bstr_k P = 1%r.
proof. 
 intros => P hp.
 apply mu_one.
 by intros x;rewrite /cpTrue;smt.
 by apply Dword.lossless.
save.

lemma sample_sk_mu_one : forall (P : Sk cpred),
(forall (y : Sk), (P y))  =>
mu sample_sk P = 1%r.
proof. 
 intros => P hp.
 apply mu_one.
 by intros x;rewrite /cpTrue;smt.
 by apply sample_sk_ll.
save.
 
lemma sample_eexp_mu_one : forall (P : Eexp cpred),
(forall (y : Eexp), (P y))  =>
mu sample_eexp P = 1%r.
proof. 
 intros => P hp.
 apply mu_one.
 by intros x;rewrite /cpTrue;smt.
 by apply sample_eexp_ll.
save.


lemma sample_esk_mu_one : forall (P : Esk cpred),
(forall (y : Esk), (P y))  =>
mu sample_esk P = 1%r.
proof. 
 intros => P hp.
 apply mu_one.
 by intros x;rewrite /cpTrue;smt.
 by apply sample_esk_ll.
save.

(* type role = Init | Resp *)
type Role = bool.

const init : bool = true.
const resp : bool = false.

op gen_pk : Sk -> Pk.
op gen_epk : Eexp -> Epk.
op gen_session_string_init : Eexp -> Sk -> Pk -> Epk -> Session_string.
op gen_session_string_resp : Eexp -> Sk -> Pk -> Epk -> Session_string.

op gsstr (x' : Eexp, a : Sk, B : Pk, Y : Epk, r : Role) = 
if r then gen_session_string_init x' a B Y 
     else gen_session_string_resp x' a B Y.

(* Data associated to started session *)
type SessionData = (Agent * Agent * Esk * Eexp * Role).

(* Partial Session ID, can be computed from SessionData *)
type PSid = (Agent * Agent * Epk * Role).

op psid_of_sessionData(sdata : SessionData) =
  let (A,B,x,x',r) = sdata in (A,B,gen_epk(x'),r).

type Sid = (Agent * Agent * Epk * Epk * Role).

op sid_of_sessionData(sdata : SessionData, Y : Epk) =
  let (A,B,x,x',r) = sdata in (A,B,gen_epk(x'),Y,r).

op psid_of_sid(sid : Sid) =
  let (A,B,X,Y,r) = sid in (A,B,X,r).

op sd_eexp(sdata : SessionData) =
  let (A,B,x,x',r) = sdata in x'.

op sd_esk(sdata : SessionData) =
  let (A,B,x,x',r) = sdata in x.

(* Strong partnering property *)
axiom strong_partnering :
forall (x', y' : Eexp, a, b : Sk, A, B : Pk, X, Y : Epk, r1, r2 : Role),
gsstr x' a B Y r1 = gsstr y' b A X r2 <=>
((a = b /\ x' = y' /\ A = B /\ X = Y /\ r1 = r2) \/
(A = gen_pk(a) /\ B = gen_pk(b) /\ X = gen_epk(x') /\ Y = gen_epk(y') /\ r1 <> r2)).

  
(* type Event = StaticRev of Agent 
              | EphemeralRev of PSid 
              | SessionRev of Sid 
              | Accept of Sid *)
type Event.

op Start : PSid -> Event.
op StaticRev : Agent -> Event.
op EphemeralRev : PSid -> Event.
op SessionRev : Sid -> Event.
op Accept : Sid -> Event.


op matching(t : Sid) = let (A,B,X,Y,r) = t in (B,A,Y,X,!r).
op partial_matching(t : Sid) = let (A,B,X,Y,r) = t in (B,A,Y,!r).


(* The (completed) session t is fresh unless *)
pred notfresh(t : Sid,  evs : Event list)  =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
  let pt = psid_of_sid t in
  let s = matching t in
  let ps = psid_of_sid s in
  (* 1. t's session key has been revealed, or *)
     List.mem (SessionRev t) evs
  (* 2. t's ephemeral secret key has been revealed, or *)
  \/ (List.mem (EphemeralRev pt) evs /\ List.mem (StaticRev t_actor) evs)
  (* 3. the session key of a matching session of t has been revealed, or *)
  \/ List.mem (SessionRev s) evs
  (* 4. the ephemeral key and static secret key of a partially matching session have
        been revealed, or *)
  \/ (List.mem (EphemeralRev ps) evs  /\ List.mem (StaticRev t_peer) evs)
  (* 5. there is neither a *)
  \/ (   (* fully matching session nor *)
         !List.mem (Accept s) evs
         (* a partially matching session and *)
      /\ (   !List.mem (Start ps) evs
          \/ (exists (z : Epk), List.mem (Accept (t_peer,t_actor,t_recvd,z,!r)) evs))
         (* the static key of t's peer has been revealed. *)
      /\ List.mem (StaticRev t_peer) evs).

(* We want to prove that notfresh is monotonic, i.e.,
   notfresh(tr,t) implies that for all extensions tr'
   of tr, notfresh(tr',t).

   The problem is that notfresh is not monotonic for all traces.
   For traces that contain collisions of ephemeral public keys,
   the following can happen:
   1. test = (A,B,X,Y,resp) completes and there is no
      session that sends Y.
   2. StaticRev(B) \in evs
   3. Later on, a session (B,A,Y) is started (Y collision) and
      test becomes fresh.

   We should be able to perform an up-to-bad step where we disallow
   this (halt if this happens or ignore Init/Resp query). Then
   No-collision is an invariant and we can also adapt nofresh such that
   nofresh'(tr,t) = nofresh(tr,t) /\ no-collision(tr) and nofresh' is
   monotonic then.

   We could define no-collision as
   forall i A B X r, evs[i] = Start(A,B,X,r)
     => X \notin evs[0..i-1]

   where X \notin evs[0..i-1] checks if X occurs in Start or Accept event, i.e.,
   forall (j < i) C D r Y. evs[j] <> Start(C,D,X,r) /\
                           evs[j] <> Accept(C,D,Y,X,r) /\
                           evs[j] <> Accept(C,D,X,Y,r) /\
*)

(* Tried to define fresh
pred fresh(t : Sid,  evs : Event list)  =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
  let s = matching t in
  let ps = psid_of_sid s in
  (* 1. No session key reveal for t *)
     (!List.mem (SessionRev t) evs)
  (* 2. Not ephemeral reveal for t *)
  /\ !(   List.mem (EphemeralRev(psid_of_sid(t))) evs) 
       (* and static reveal for t_actor *)
       /\ List.mem (StaticRev t_actor) evs
  (* 3. Not session key reveal for matching session (if it exists) *)
  /\ (!List.mem (SessionRev s) evs)
  (* 4. If there is fully matching session or a partially matching session*)
  /\ ((   (    List.mem (Accept s) evs
           \/ (   List.mem (Start ps) evs)
               /\ (forall (z : Epk),
                     !List.mem (Accept (t_peer, t_actor, t_recvd, z, !r)) evs))
        (* then not both ephemeral and static revealed *)
        /\ !(List.mem (EphemeralRev ps) evs
              /\ List.mem (StaticRev t_peer) evs)))
         (* If there is neither a fully nor a partially matching session, *)
      \/ ( !List.mem (Accept s) evs /\
            (!List.mem (Start ps) evs
             \/ (exists (z : Epk), List.mem (Accept (t_peer,t_actor,t_recvd,z,!r)) evs))
          (* then no static reveal. *)
          /\ !List.mem (StaticRev t_peer) evs).
*)

op fresh(t : Sid,  evs : Event list)  =
  let (t_actor, t_peer, t_epk, t_recvd, r) = t in
     (!List.mem (SessionRev t) evs)    (* no session key reveal for t *)
  /\ !(List.mem (EphemeralRev(psid_of_sid(t))) evs) 
  /\ List.mem (StaticRev t_actor) evs  (* not x and a *)
  /\ (let s = matching(t) in (* There is a matching session s *)
         (   List.mem (Accept s) evs
          /\ !List.mem (SessionRev s) evs     (* no session key reveal for s *)
          /\ !(List.mem (EphemeralRev(psid_of_sid(s))) evs
              /\ List.mem (StaticRev t_peer) evs))          (* not y and b *)
         (* There is no matching session *)
      \/ (   !List.mem (Accept s) evs
          /\ !List.mem (StaticRev t_peer) evs)) (* not b *)
  /\  (let ps = partial_matching(t) in (* There is a partially matching session s *)
         (   List.mem (Start ps) evs
          /\ !(List.mem (EphemeralRev(ps))) evs
              /\ List.mem (StaticRev t_peer) evs)         (* not y and b *)
         (* There is no possibly matching session *)
      \/ (   !List.mem (Start ps) evs
          /\ !List.mem (StaticRev t_peer) evs)).

axiom Event_no_junk:
  forall (Ev : Event),
       (exists (A : Agent), Ev = StaticRev(A))
    \/ (exists (s : PSid), Ev = EphemeralRev(s))
    \/ (exists (s : Sid), Ev = SessionRev(s))
    \/ (exists (s : Sid), Ev = Accept(s))
    \/ (exists (s : PSid), Ev = Start(s)).

axiom Event_free1: forall (A : Agent, s : PSid), StaticRev(A) <> EphemeralRev(s).
axiom Event_free2: forall (A : Agent, s : Sid), StaticRev(A) <> SessionRev(s).
axiom Event_free3: forall (A : Agent, s : Sid), StaticRev(A) <> Accept(s).
axiom Event_free4: forall (s1 : PSid, s2 : Sid), EphemeralRev(s1) <> SessionRev(s2).
axiom Event_free5: forall (s1 : PSid, s2 : Sid), EphemeralRev(s1) <> Accept(s2).
axiom Event_free6: forall (s1, s2 : Sid), SessionRev(s1) <> Accept(s2).
axiom Event_free7: forall (s1 : PSid, s2 : Sid), Start(s1) <> SessionRev(s2).
axiom Event_free8: forall (s1 : PSid, s2 : Sid), Start(s1) <> Accept(s2).
axiom Event_free9: forall (A : Agent, s : PSid), StaticRev(A) <> Start(s).
axiom Event_free10: forall (s1 s2 : PSid), Start(s1) <> EphemeralRev(s2).

 


axiom StaticRev_inj:    forall (A, B : Agent), 
 StaticRev(A) = StaticRev(B) => A = B.

axiom EphemeralRev_inj: forall (s1, s2 : PSid), 
 EphemeralRev(s1) = EphemeralRev(s2) => s1 = s2.

axiom SessionRev_inj:   forall (s1, s2 : Sid), 
 SessionRev(s1) = SessionRev(s2) => s1 = s2.

axiom Accept_inj :  forall (s1, s2 : Sid), 
 Accept(s1) = Accept(s2) => s1 = s2.


axiom Start_inj: forall (s1, s2 : PSid), 
 Start(s1) = Start(s2) => s1 = s2.

const qSess : int.
const qH1 : int.
const qH2 : int.
const qSessKR : int.
const qEphKR : int.
const qAg : int.

axiom qSess_pos : 0 < qSess.
axiom qH1_pos : 0 < qH1.
axiom qH2_pos : 0 < qH2.
axiom qSessKR_pos : 0 < qSessKR.
axiom qEphKR_pos : 0 < qEphKR.
axiom qAg_pos : 0 < qAg.


lemma absurd : forall P Q, !P => P => Q by smt.

lemma not_or_and :
forall P Q, (! (P \/ Q)) = (! P /\ ! Q) by [].

lemma not_and_or :
forall P Q, (! (P /\ Q)) = (! P \/ ! Q) by [].

lemma diff_cons : forall (x y : 'a)(xs : 'a list),
! mem x xs => 
mem x (y::xs) => y = x by smt.

lemma notfresh_fresh :
forall t tr e,
notfresh t tr =>
!notfresh t (e::tr) =>
e = Accept (matching t) \/ 
e = Start (psid_of_sid (matching t)).
proof.
 intros => t.
 elim/tuple5_ind t => t_actor t_peer t_sent t_rcvd role cl tr e hnfresh hfresh.
 clear cl t.
 generalize hfresh;rewrite /notfresh /= !not_or_and !not_and_or !not_or_and /=; 
   progress.
 generalize hnfresh;rewrite /notfresh /= => [|[|[|[|]]]];first 4 by smt.
 intros => [hmemacc][] hnmem_or hmem.
 generalize H3 =>  [hnmem | [[hmem2] hnex |]];first by left;apply (diff_cons _ _ tr).
 right.
 generalize hnmem_or => [hnmem2 |].
 apply (diff_cons _ _ tr) => //.
 intros => [z] hmemz.
 cut  abs : (exists (z : Epk),
           mem (Accept (t_peer, t_actor, t_rcvd, z, ! role)) (e :: tr))
  by exists z; smt.
  by smt.
save.


type EId = int.

module type Proto ={
 fun initialize() : Pk set
 fun h1_a (sstring : Session_string) : Key option
 fun h2_a (a : Sk, x : Esk) : Eexp option
 fun init1(i : EId, A : Agent, B : Agent) : Epk option
 fun init2(i : EId, Y : Epk) : unit
 fun resp(i : EId, B : Agent, A : Agent, X : Epk) : Epk option
 fun staticReveal(A : Agent) : Sk option
 fun ephemeralReveal(i : EId) : Esk option
 fun sessionReveal(i : EId) : Key option
 fun computeKey(i : EId) : Key option
 fun isCompleteAndFresh(i : EId) : bool
 fun setTest (i : EId) : unit
}.

module type ProtoA ={
 fun h1_a (sstring : Session_string) : Key option
 fun h2_a (a : Sk, x : Esk) : Eexp option
 fun init1(i : EId, A : Agent, B : Agent) : Epk option
 fun init2(i : EId, Y : Epk) : unit
 fun resp(i : EId, B : Agent, A : Agent, X : Epk) : Epk option
 fun staticReveal(A : Agent) : Sk option
 fun ephemeralReveal(i : EId) : Esk option
 fun sessionReveal(i : EId) : Key option
}.


module type Adv (P : ProtoA) = {
 fun choose(s : Pk set) : EId
 fun guess(k : Key option) : bool
}.

module ECK(P : Proto, A_ : Adv)  = {
 var test_id : EId option 
  module A = A_(P)
   fun main() : bool = {
   var b : bool;
   var pks : Pk set;
   var eid : EId;
   var keyo : Key option;
   var key : Key;
   var fr : bool;
   var b' : bool = false;
   test_id = None;
   pks = P.initialize();
   eid = A.choose(pks);
   fr = P.isCompleteAndFresh(eid);
   b = ${0,1};
   if (fr) {
    test_id = Some eid;
    P.setTest(eid);
    if (b) keyo = P.computeKey(eid);
    else {
     key = $sample_bstr_k;
     keyo = Some key;
    }
    b' = A.guess(keyo);
    fr = P.isCompleteAndFresh(eid);
   }
   return (fr && b = b');
  }
}.

module AKE : Proto = {
 var cSess, cH1, cH2, cSessKR, cEpkKR : int (* counters for queries *)
 var mH1 : (Session_string, Key) map
 var sH1 : Session_string set
 var mH2 : ((Sk * Esk), Eexp) map
 var sH2 : (Sk * Esk) set
 var mSk : (Agent, Sk) map
 var mStarted   : (EId, SessionData) map
 var mCompleted : (EId, Epk)         map 
 var evs : Event list
 var test : Sid option
 var testid : EId option

 fun h1(sstring : Session_string) : Key = {
  var ke : Key;
  ke = $sample_bstr_k;
 if (!in_dom sstring mH1) {
   mH1.[sstring] = ke;
 }
 return Option.proj ((mH1.[sstring]));
 }
 fun h1_a(sstring : Session_string) : Key option = {
   var r : Key option = None;
   var ks : Key;
   if (cH1 < qH1) {
   cH1 = cH1 + 1;
   ks = h1(sstring);
   r = Some(ks);
   sH1 = add sstring sH1;
  }
    return r;
 }

  fun h2(a : Sk, x : Esk) : Eexp = {
    var e : Eexp;
    e = $sample_eexp;
    if (!in_dom (a,x) mH2) {
      cH2 = cH2 + 1;
      mH2.[(a,x)] = e;
    }
    return proj (mH2.[(a,x)]);
  }

  fun h2_a(a : Sk, x : Esk) : Eexp option = {
    var r : Eexp option = None;
    var xe : Eexp;
    if (cH2 < qH2) {
      cH2 = cH2 + 1;
      xe = h2(a,x);
      r = Some(xe);
      sH2 = add (a,x) sH2;
    }
    return r;
  }


  fun initialize() : Pk set = {
    var l : Pk set = FSet.empty;
    var i : int = 0;
    var ska : Sk;
    var pka : Pk;
    while (i < qAg) {
      ska = $sample_sk;
      pka = gen_pk(ska);
      l = add pka l;
      mSk.[pka] = ska;
    } 
    cSess = 0;
    cH1 = 0;
    cH2 = 0;
    cSessKR = 0; 
    cEpkKR = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    evs = [];
    test = None;
    testid = None;
    return l;
  }

  (******************************************************************)
  (* Protocol Steps                                                 *)
  (******************************************************************)

   (* contains only received message, remaining information in mStarted *)
   (* invariant: dom(mComplete) <= dom(mStarted) *)

  fun init1(i : EId, A : Agent, B : Agent) : Epk option = {
    var xesk : Esk;
    var x' : Eexp;
    var xepk : Epk;
    var r : Epk option = None; 
    (* break if one agent is invalid or if Eid not fresh *)
    if (cSess < qSess && in_dom A mSk && in_dom B mSk && !in_dom i mStarted &&
     (let  evs' = Start (A,B,dEpk,init) :: evs in
        test <> None => fresh (proj test) evs)) {
      cSess = cSess + 1;
      xesk  = $sample_esk;
     x' = h2(proj (mSk.[A]),xesk);
      xepk = gen_epk(x');
      mStarted.[i] = (A,B,xesk,x',init);
      r = Some(xepk);
      evs = Start(psid_of_sessionData(proj mStarted.[i]))::evs;
    }
    return r;
  }


  fun resp(i : EId, B : Agent, A : Agent, X : Epk) : Epk option = {
    var yesk : Esk;
    var y' : Eexp;
    var yepk : Epk;
    var r : Epk option = None; 
    (* break if one agent is invalid or if Eid not fresh *)
    if (cSess < qSess && in_dom A mSk && in_dom B mSk && !in_dom i mStarted &&
        !in_dom i mCompleted &&
      (let  evs' = Accept (B,A,dEpk,X,resp) :: evs in
        test <> None => fresh (proj test) evs)) {
      cSess = cSess + 1;
      yesk  = $sample_esk;
      y' = h2(proj (mSk.[B]),yesk);
      yepk = gen_epk(y');
      mStarted.[i] = (B,A,yesk,y',resp);
      mCompleted.[i] = X;
      r = Some(yepk);
      evs = Accept(sid_of_sessionData (proj mStarted.[i]) X)::evs;
    }
    return r;
  }

  fun init2(i : EId, Y : Epk) : unit = {
    if (!in_dom i mCompleted && in_dom i mStarted &&
    (let  evs' = Accept(sid_of_sessionData(proj mStarted.[i]) Y):: evs in
     test <> None => fresh (proj test) evs)) {
     mCompleted.[i] = Y;
     evs = Accept(sid_of_sessionData(proj mStarted.[i]) Y)::evs;
    }
   }

  (******************************************************************)
  (* Key Reveals                                                    *)
  (******************************************************************)

  fun staticReveal(A : Agent) : Sk option = {
    var r : Sk option = None;
    if (in_dom A mSk && 
    (let  evs' = StaticRev(A) :: evs in
     test <> None => fresh (proj test) evs)) { 
     r = (mSk.[A]);
     evs = StaticRev(A)::evs;
    }
    return r;
  }

  fun ephemeralReveal(i : EId) : Esk option = {
    var r : Esk option = None;
    if (in_dom i mStarted  && cEpkKR < qEphKR &&
    (let  evs' = EphemeralRev(psid_of_sessionData(proj mStarted.[i])) :: evs in
     test <> None => fresh (proj test) evs)) {
      r = Some(sd_esk(proj mStarted.[i]));
      evs = EphemeralRev(psid_of_sessionData(proj mStarted.[i]))::evs;
      cEpkKR = cEpkKR + 1;
    }
    return r;
   }

  fun computeKey(i : EId) : Key option = {
    var rv : Key option = None;
    var xepk : Epk;
    var a, b : Agent;
    var r : Role;
    var x' : Eexp;
    var xesk : Esk;
    var key : Key;
    if (in_dom i mCompleted) {
      (a,b,xesk,x',r) = proj mStarted.[i];
      key  = h1(gsstr x' (proj mSk.[a]) b (proj mCompleted.[i]) r);
      rv = Some key;
    }
    return rv;
  }
  fun sessionReveal(i : EId) : Key option = {
    var r : Key option = None;
    var s : Sid;
    if (in_dom i mCompleted && cSessKR < qSessKR &&
    (let  evs' = SessionRev(sid_of_sessionData 
      (proj mStarted.[i]) (proj mCompleted.[i]))::evs in
     test <> None => fresh (proj test) evs)) {
    s = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
    evs = SessionRev(sid_of_sessionData 
     (proj mStarted.[i]) (proj mCompleted.[i]))::evs;
    cSessKR = cSessKR + 1;
    r = computeKey(i);
   }
   return r;
  }

  fun isCompleteAndFresh(i : EId) : bool = {
   var s : Sid;
   var b : bool = false;
   if (in_dom i mCompleted /\ in_dom i mStarted) {
    s = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
    b = fresh s evs;
   }
   return b;
  }
  fun setTest(i : EId) : unit = {
   var s : Sid = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
   testid = Some i;
   test = Some s;
  }
}.


section.

declare module A : Adv{AKE,ECK}.

axiom ll :
forall (P <: ProtoA{A}),
  islossless P.h1_a =>
  islossless P.h2_a =>
  islossless P.init1 =>
  islossless P.init2 =>
  islossless P.resp =>
  islossless P.staticReveal =>
  islossless P.ephemeralReveal =>
  islossless P.sessionReveal => islossless A(P).guess.


(* Helper operator *)
op getStringFromEId (i : EId)(mStarted : (EId, SessionData) map) 
                    (mCompleted : (EId, Epk) map)  
                    (mSk : (Agent, Sk) map) = 
let (a,b,xesk,x',r) = proj mStarted.[i] in
gsstr x' (proj mSk.[a]) b (proj mCompleted.[i]) r.


lemma getStringFromEIdUpdStarted :
forall i mStrt j mCmplt sessInf mSk,
in_dom i mStrt =>
! in_dom j mStrt => 
getStringFromEId i mStrt mCmplt mSk =  
getStringFromEId i mStrt.[j <- sessInf] mCmplt mSk.
proof.
 intros => i mStrt j mCmplt sessInf mSk hiindom hjnindom.
 cut hneq: i <> j by smt.
 rewrite /getStringFromEId /=.
 by cut ->: mStrt.[i] = mStrt.[j<-sessInf].[i] by smt.
qed.

lemma getStringFromEIdUpdCompleted :
forall i mStrt j mCmplt sessInf mSk,
in_dom i mCmplt =>
! in_dom j mCmplt => 
getStringFromEId i mStrt mCmplt mSk =  
getStringFromEId i mStrt mCmplt.[j <- sessInf] mSk.
proof.
 intros => i mStrt j mCmplt sessInf mSk hiindom hjnindom.
 cut hneq: i <> j by smt.
 rewrite /getStringFromEId /=.
 by cut ->: mCmplt.[i] = mCmplt.[j<-sessInf].[i] by smt.
qed.

lemma le_congr : forall (a b c d : real), 
  a <= c => b <= d => a + b <= c + d by [].


local module G1 : Proto = {
 var cSess, cH1, cH2, cSessKR, cEpkKR : int (* counters for queries *)
 var mH1 : (Session_string, Key) map
 var sH1 : Session_string set
 var mH2 : ((Sk * Esk), Eexp) map
 var sH2 : (Sk * Esk) set
 var mSk : (Agent, Sk) map
 var mStarted   : (EId, SessionData) map
 var mCompleted : (EId, Epk)         map 
 var evs : Event list
 var test : Sid option
 var testid : EId option

 fun h1(sstring : Session_string) : Key = {
  var ke : Key;
  ke = $sample_bstr_k;
 if (!in_dom sstring mH1) {
   mH1.[sstring] = ke;
 }
 return Option.proj ((mH1.[sstring]));
 }
 fun h1_a(sstring : Session_string) : Key option = {
   var r : Key option = None;
   var ks : Key;
   if (cH1 < qH1) {
   cH1 = cH1 + 1;
   ks = h1(sstring);
   r = Some(ks);
   sH1 = add sstring sH1;
  }
    return r;
 }

  fun h2(a : Sk, x : Esk) : Eexp = {
    var e : Eexp;
    e = $sample_eexp;
    if (!in_dom (a,x) mH2) {
      cH2 = cH2 + 1;
      mH2.[(a,x)] = e;
    }
    return proj (mH2.[(a,x)]);
  }

  fun h2_a(a : Sk, x : Esk) : Eexp option = {
    var r : Eexp option = None;
    var xe : Eexp;
    if (cH2 < qH2) {
      cH2 = cH2 + 1;
      xe = h2(a,x);
      r = Some(xe);
      sH2 = add (a,x) sH2;
    }
    return r;
  }


  fun initialize() : Pk set = {
    var l : Pk set = FSet.empty;
    var i : int = 0;
    var ska : Sk;
    var pka : Pk;
    while (i < qAg) {
      ska = $sample_sk;
      pka = gen_pk(ska);
      l = add pka l;
      mSk.[pka] = ska;
    } 
    cSess = 0;
    cH1 = 0;
    cH2 = 0;
    cSessKR = 0; 
    cEpkKR = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    evs = [];
    test = None;
    testid = None;
    return l;
  }

  (******************************************************************)
  (* Protocol Steps                                                 *)
  (******************************************************************)

   (* contains only received message, remaining information in mStarted *)
   (* invariant: dom(mComplete) <= dom(mStarted) *)

  fun init1(i : EId, A : Agent, B : Agent) : Epk option = {
    var xesk : Esk;
    var x' : Eexp;
    var xepk : Epk;
    var r : Epk option = None; 
    (* break if one agent is invalid or if Eid not fresh *)
    if (cSess < qSess && in_dom A mSk && in_dom B mSk && !in_dom i mStarted &&
     (let  evs' = Start (A,B,dEpk,init) :: evs in
        test <> None => fresh (proj test) evs)) {
      cSess = cSess + 1;
      xesk  = $sample_esk;
      x' = h2(proj (mSk.[A]),xesk);
      xepk = gen_epk(x');
      mStarted.[i] = (A,B,xesk,x',init);
      r = Some(xepk);
      evs = Start(psid_of_sessionData(proj mStarted.[i]))::evs;
    }
    return r;
  }


  fun resp(i : EId, B : Agent, A : Agent, X : Epk) : Epk option = {
    var yesk : Esk;
    var y' : Eexp;
    var yepk : Epk;
    var r : Epk option = None; 
    (* break if one agent is invalid or if Eid not fresh *)
    if (cSess < qSess && in_dom A mSk && in_dom B mSk && !in_dom i mStarted &&
        !in_dom i mCompleted &&
      (let  evs' = Accept (B,A,dEpk,X,resp) :: evs in
        test <> None => fresh (proj test) evs)) {
      cSess = cSess + 1;
      yesk  = $sample_esk;
      y' = h2(proj (mSk.[B]),yesk);
      yepk = gen_epk(y');
      mStarted.[i] = (B,A,yesk,y',resp);
      mCompleted.[i] = X;
      r = Some(yepk);
      evs = Accept(sid_of_sessionData (proj mStarted.[i]) X)::evs;
    }
    return r;
  }

  fun init2(i : EId, Y : Epk) : unit = {
    if (!in_dom i mCompleted && in_dom i mStarted &&
    (let  evs' = Accept(sid_of_sessionData(proj mStarted.[i]) Y):: evs in
     test <> None => fresh (proj test) evs)) {
     mCompleted.[i] = Y;
     evs = Accept(sid_of_sessionData(proj mStarted.[i]) Y)::evs;
    }
   }

  (******************************************************************)
  (* Key Reveals                                                    *)
  (******************************************************************)

  fun staticReveal(A : Agent) : Sk option = {
    var r : Sk option = None;
    if (in_dom A mSk && 
    (let  evs' = StaticRev(A) :: evs in
     test <> None => fresh (proj test) evs)) { 
     r = (mSk.[A]);
     evs = StaticRev(A)::evs;
    }
    return r;
  }

  fun ephemeralReveal(i : EId) : Esk option = {
    var r : Esk option = None;
    if (in_dom i mStarted  && cEpkKR < qEphKR &&
    (let  evs' = EphemeralRev(psid_of_sessionData(proj mStarted.[i])) :: evs in
     test <> None => fresh (proj test) evs)) {
      r = Some(sd_esk(proj mStarted.[i]));
      evs = EphemeralRev(psid_of_sessionData(proj mStarted.[i]))::evs;
      cEpkKR = cEpkKR + 1;
    }
    return r;
   }

  fun computeKeyKR(i : EId) : Key option = {
    var rv : Key option = None;
    var xepk : Epk;
    var a, b : Agent;
    var r : Role;
    var x' : Eexp;
    var xesk : Esk;
    var key : Key;
    if (in_dom i mCompleted) {
      (a,b,xesk,x',r) = proj mStarted.[i];
      key  = h1(gsstr x' (proj mSk.[a]) b (proj mCompleted.[i]) r);
      rv = Some key;
    }
    return rv;
  }

  fun computeKey(i : EId) : Key option = {
    var rv : Key option = None;
    var xepk : Epk;
    var a, b : Agent;
    var r : Role;
    var x' : Eexp;
    var xesk : Esk;
    var key : Key;
    if (in_dom i mCompleted) {
      (a,b,xesk,x',r) = proj mStarted.[i];
      key  = $sample_bstr_k;
      rv = Some key;
    }
    return rv;
  }

  fun sessionReveal(i : EId) : Key option = {
    var r : Key option = None;
    var s : Sid;
    if (in_dom i mCompleted && cSessKR < qSessKR &&
    (let  evs' = SessionRev(sid_of_sessionData 
      (proj mStarted.[i]) (proj mCompleted.[i]))::evs in
     test <> None => fresh (proj test) evs)) {
    s = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
    evs = SessionRev(sid_of_sessionData 
     (proj mStarted.[i]) (proj mCompleted.[i]))::evs;
    cSessKR = cSessKR + 1;
    r = computeKeyKR(i);
   }
   return r;
  }

  fun isCompleteAndFresh(i : EId) : bool = {
   var s : Sid;
   var b : bool = false;
   if (in_dom i mCompleted /\ in_dom i mStarted) {
    s = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
    b = fresh s evs;
   }
   return b;
  }
  fun setTest(i : EId) : unit = {
   var s : Sid = sid_of_sessionData (proj mStarted.[i]) (proj mCompleted.[i]);
   testid = Some i;
   test = Some s;
  }
}.



local equiv Eq_AKE_G1 :
ECK(AKE,A).main ~ ECK(G1,A).main : ={glob A} ==> 
res{1} =>
(!(ECK.test_id <> None /\ 
   Map.in_dom (getStringFromEId (proj ECK.test_id) 
              G1.mStarted G1.mCompleted G1.mSk) G1.mH1) => res){2}.
proof.
 fun.
seq 4 4:
 (={glob A,eid,b'} /\  
  AKE.cH2{1} = G1.cH2{2} /\
  AKE.cH1{1} = G1.cH1{2} /\
  AKE.cSessKR{1} = G1.cSessKR{2} /\
  AKE.cSess{1} = G1.cSess{2} /\
  AKE.cEpkKR{1} = G1.cEpkKR{2} /\
  AKE.mH1{1} = G1.mH1{2} /\
  AKE.sH1{1} = G1.sH1{2} /\
  AKE.mH2{1} = G1.mH2{2} /\
  AKE.mSk{1} = G1.mSk{2} /\ 
  AKE.mStarted{1} = G1.mStarted{2} /\ 
  AKE.mCompleted{1} = G1.mCompleted{2} /\
  AKE.test{1} = G1.test{2} /\
  AKE.testid{1} = G1.testid{2} /\
  AKE.evs{1} = G1.evs{2}); first by eqobs_in.

seq 2 2:
 (={glob A,b,b',fr,eid} /\  
  AKE.cH2{1} = G1.cH2{2} /\
  AKE.cH1{1} = G1.cH1{2} /\
  AKE.cSessKR{1} = G1.cSessKR{2} /\
  AKE.cSess{1} = G1.cSess{2} /\
  AKE.cEpkKR{1} = G1.cEpkKR{2} /\
  AKE.mH1{1} = G1.mH1{2} /\
  AKE.sH1{1} = G1.sH1{2} /\
  AKE.mH2{1} = G1.mH2{2} /\
  AKE.mSk{1} = G1.mSk{2} /\ 
  AKE.mStarted{1} = G1.mStarted{2} /\ 
  AKE.mCompleted{1} = G1.mCompleted{2} /\
  AKE.test{1} = G1.test{2} /\
  AKE.testid{1} = G1.testid{2} /\
  AKE.evs{1} = G1.evs{2} /\ 
  (fr{2} => in_dom eid{2} G1.mStarted{2} /\ in_dom eid{2} G1.mCompleted{2}) /\
 (fr{1} => in_dom eid{1} AKE.mStarted{1} /\ in_dom eid{1} AKE.mCompleted{1})).
by inline AKE.isCompleteAndFresh G1.isCompleteAndFresh;rnd;wp;skip;progress;smt.
if => //;inline AKE.isCompleteAndFresh G1.isCompleteAndFresh;wp.
inline AKE.setTest G1.setTest.
sp.
if;last first.
seq 3 3: ( (={glob A,b,b',fr,eid, ECK.test_id} /\  
  AKE.cH2{1} = G1.cH2{2} /\
  AKE.cH1{1} = G1.cH1{2} /\
  AKE.cSessKR{1} = G1.cSessKR{2} /\
  AKE.cSess{1} = G1.cSess{2} /\
  AKE.cEpkKR{1} = G1.cEpkKR{2} /\
  AKE.mH1{1} = G1.mH1{2} /\
  AKE.sH1{1} = G1.sH1{2} /\
  AKE.mH2{1} = G1.mH2{2} /\
  AKE.mSk{1} = G1.mSk{2} /\ 
  AKE.mStarted{1} = G1.mStarted{2} /\ 
  AKE.mCompleted{1} = G1.mCompleted{2} /\
  AKE.test{1} = G1.test{2} /\
  AKE.testid{1} = G1.testid{2} /\
  AKE.evs{1} = G1.evs{2})).
eqobs_in => //.
by progress.
by progress.

call 
(_: Map.in_dom (getStringFromEId (proj ECK.test_id) 
              G1.mStarted G1.mCompleted G1.mSk) G1.mH1,
  (={ECK.test_id} /\  
  AKE.cH2{1} = G1.cH2{2} /\
  AKE.test{1} = G1.test{2} /\
  AKE.testid{1} = G1.testid{2} /\
  AKE.cH1{1} = G1.cH1{2} /\
  AKE.cSessKR{1} = G1.cSessKR{2} /\
  AKE.cSess{1} = G1.cSess{2} /\
  AKE.cEpkKR{1} = G1.cEpkKR{2} /\
  AKE.sH1{1} = G1.sH1{2} /\
  AKE.mH2{1} = G1.mH2{2} /\
  AKE.mSk{1} = G1.mSk{2} /\ 
  AKE.mStarted{1} = G1.mStarted{2} /\ 
  AKE.mCompleted{1} = G1.mCompleted{2} /\
  AKE.evs{1} = G1.evs{2} /\ 
  Map.eq_except AKE.mH1{1} G1.mH1{2} 
 (getStringFromEId (proj ECK.test_id) 
  G1.mStarted G1.mCompleted G1.mSk){2} /\ 
  ECK.test_id{2} <> None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
  in_dom (proj ECK.test_id{2}) G1.mCompleted{2}),
  ECK.test_id{2} <> None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
  in_dom (proj ECK.test_id{2}) G1.mCompleted{2}).

  by apply ll.
  (* h1_a *: relational spec *)
  fun;sp;if => //;inline AKE.h1 G1.h1;wp;rnd;wp;skip; progress => //; smt.

  (* h1_a lossless on the left *)
  intros => &2 H;fun. 
  sp.
  if.
  inline AKE.h1;wp;rnd.
  by intros => &m;apply Key.Dword.lossless.
  by wp;skip;smt.
  by skip;smt.
 
 (* h1_a on the right preserves bad *)
  intros => &1; fun; sp; wp; if.
  inline G1.h1;wp;rnd;wp;skip;progress => //=.
  by apply sample_bstr_k_mu_one => y /=; smt.
  by skip;progress.

 (*h2_a relational spec *)
  fun.
  eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2} /\
   AKE.test{1} = G1.test{2} /\
   AKE.testid{1} = G1.testid{2})
  (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\! ECK.test_id{2} = None /\ 
       in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
       in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id,r} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2} /\
  AKE.test{1} = G1.test{2} /\
  AKE.testid{1} = G1.testid{2}).
(* h2_a lossless on the left *)  
  intros => &2 h; fun; sp; if; wp => //.
  inline AKE.h2;wp.
  rnd => //.  
  by intros => _;apply sample_eexp_ll.
  by wp; skip.


(* h2_a preserves bad on the right *)
  intros => &1; fun; sp; if.
  inline G1.h2;wp;rnd;first by intros => _;apply sample_eexp_ll.
  by wp;skip;progress;smt.
  by skip; progress; smt.

(* init1 relational spec *)
  fun.
  eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2})
  (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\
  ! ECK.test_id{2} = None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
    in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id,r} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.test{1} = G1.test{2} /\
    AKE.testid{1} = G1.testid{2} /\
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2}).
(* init1 lossless on the left *)  
  intros => &2 H; fun; sp; if.
   inline AKE.h2; wp => //; rnd => //.  
  by intros => _;apply sample_eexp_ll.
  by wp; rnd; wp; skip; smt.
  by skip.

   (* init1 preserves bad on the right *)  
  intros => &1;fun; sp; if.
   inline G1.h2; do 2! (wp; rnd); wp; skip; progress => /=.
   by apply sample_esk_mu_one => x /=;apply sample_eexp_mu_one => y /=;
   rewrite -getStringFromEIdUpdStarted //;smt.
   by skip => //.

(* init2 relational spec *)
   fun.
   eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2})
  (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\
  ! ECK.test_id{2} = None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
    in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.test{1} = G1.test{2} /\
    AKE.testid{1} = G1.testid{2} /\
    AKE.evs{1} = G1.evs{2}).
(* init2 lossless on the left *)  
   by intros => &2 H; fun; wp; skip.
   (* init2 preserves bad on the right *)  
   by intros => &1; fun; wp;skip;progress; smt.
(* resp relational spec *)
  fun.
  eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2})
    (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\
  ! ECK.test_id{2} = None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
    in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id,r} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.test{1} = G1.test{2} /\
    AKE.testid{1} = G1.testid{2} /\
    AKE.evs{1} = G1.evs{2}).
(* resp lossless on the left *)  
  intros => &2 H; fun; sp; if.
  inline AKE.h2;wp; rnd => //;first by intros => _;apply sample_eexp_ll.
  by wp; rnd; wp; skip; smt.
  by skip.
   (* resp preserves bad on the right *)  
  intros => &1; fun; sp; if; last by skip.
   inline G1.h2; do 2! (wp; rnd); wp; skip; progress => /=.
   by apply sample_esk_mu_one => x /=;apply sample_eexp_mu_one => y /=;
    rewrite -getStringFromEIdUpdStarted //;try smt.


   (* staticReveal relational spec *)
   fun.
   eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2})
  (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\
  ! ECK.test_id{2} = None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
    in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id,r} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.test{1} = G1.test{2} /\
    AKE.testid{1} = G1.testid{2} /\
    AKE.evs{1} = G1.evs{2}).
   (* staticReveal lossless on the left *)
   by intros => &2 hdom;fun; wp.
   (* staticReveal preserves bad on the right *)
   by intros &1; fun; wp; skip.
   (* ephReveal relational spec *)
   fun.
   eqobs_in (
  ={ECK.test_id} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.evs{1} = G1.evs{2})
  (eq_except AKE.mH1{1} G1.mH1{2}
    (getStringFromEId (proj ECK.test_id{2}) G1.mStarted{2} G1.mCompleted{2}
       G1.mSk{2}) /\
  ! ECK.test_id{2} = None /\ in_dom (proj ECK.test_id{2}) G1.mStarted{2} /\
    in_dom (proj ECK.test_id{2}) G1.mCompleted{2}) :
( ={ECK.test_id,r} /\ AKE.cH2{1} = G1.cH2{2} /\ AKE.cH1{1} = G1.cH1{2} /\
    AKE.cSessKR{1} = G1.cSessKR{2} /\ AKE.cSess{1} = G1.cSess{2} /\
    AKE.cEpkKR{1} = G1.cEpkKR{2} /\  AKE.sH1{1} = G1.sH1{2} /\
    AKE.mH2{1} = G1.mH2{2} /\ AKE.mSk{1} = G1.mSk{2} /\ 
    AKE.mStarted{1} = G1.mStarted{2} /\ AKE.mCompleted{1} = G1.mCompleted{2} /\
    AKE.test{1} = G1.test{2} /\
    AKE.testid{1} = G1.testid{2} /\
    AKE.evs{1} = G1.evs{2}).
   (* ephReveal preserves bad on the right *)
   by intros => &2 hdom;fun; wp.
   (* staticReveal preserves bad on the right *)
   by intros &1; fun; wp; skip.
   (* sessionReveal relational spec *)
   fun; sp; if => //.
   inline AKE.computeKey G1.computeKeyKR; sp; if => //.
    by inline AKE.h1 G1.h1; wp; rnd; wp; skip; progress; smt.
    by wp; skip; progress; smt.

   (* sessionReveal lossless left *)
   intros => &2 h; fun; sp; if => //.
   inline AKE.computeKey AKE.h1.  
   sp; if => //; wp => //. 
    by rnd; try wp => //; rewrite -Word.Dword.lossless;smt.

   (* sessionReveal preserves bad on the right *)
   intros => &1; fun; sp; if => //; wp => //.
   inline G1.computeKeyKR G1.h1; sp; if => //; try wp => //.
  wp; rnd => //; wp; skip; progress.
  apply sample_bstr_k_mu_one => //; smt.

  (* Main *)
  rewrite /=;inline AKE.computeKey G1.computeKey; sp.
  rcondt{1} 1.
   intros => &m;skip;progress;elim (H _) => //.
  rcondt{2} 1.
   intros => &m;skip;progress;elim (H _) => //.
   by inline AKE.h1; wp; rnd; wp; skip; progress; smt.
save.

local lemma Pr1 &m:
Pr[ECK(AKE,A).main() @ &m : res] <= 
Pr[ECK(G1,A).main() @ &m : res] +
Pr[ECK(G1,A).main() @ &m : 
(ECK.test_id <> None /\ 
   Map.in_dom (getStringFromEId (proj ECK.test_id) 
              G1.mStarted G1.mCompleted G1.mSk) G1.mH1)].
proof.
 apply (Real.Trans _ 
 Pr[ECK(G1, A).main() @ &m : res \/
   (ECK.test_id <> None /\
   in_dom
     (getStringFromEId (proj ECK.test_id) G1.mStarted G1.mCompleted G1.mSk)
     G1.mH1)] _ _ _).
  by equiv_deno  Eq_AKE_G1=> //;first smt.
  by rewrite Pr mu_or;smt.
save.
