require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.
require import Real.

require import AKE_defs.

(*{ Initial game and security definition *)

(* The initial module: we keep it simple and inline the
   definitions of h1 and h2. *)
module AKE(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mStarted   : (Sidx, Sdata) map  (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  
  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
        cH1 = cH1 + 1;
        mH1.[(a,x)] = e;
      } 
      return proj mH1.[(a,x)];
    }

    fun h1_a(a : Sk, x : Esk) : Eexp option = {
      var r : Eexp option = None;
      var xe : Eexp;
      if (cH1 < qH1) {
        cH1 = cH1 + 1;
        sH1 = add (a,x) sH1;
        xe = h1(a,x);
        r = Some(xe);
      }
      return r;
    }

    fun h2(sstring : Sstring) : Key = {
      var ke : Key;
      ke = $sample_Key;
      if (!in_dom sstring mH2) {
        mH2.[sstring] = ke;
      }
      return proj mH2.[sstring];
    }
 
    fun h2_a(sstring : Sstring) : Key option = {
      var r : Key option = None;
      var ks : Key;
      if (cH2 < qH2) {
        cH2 = cH2 + 1;
        sH2 = add sstring sH2;
        ks = h2(sstring);
        r = Some(ks);
      }
      return r;
    }

    fun init1(i : Sidx, A : Agent, B : Agent) : Epk option = {
      var x : Esk;
      var x' : Eexp;
      var pX : Epk;
      var r : Epk option = None; 
      if (cSession < qSession && in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        cSession = cSession + 1;
        x  = $sample_Esk;
        x' = h1(proj (mSk.[A]),x);
        pX = gen_epk(x');
        mStarted.[i] = (A,B,x,x',init);
        r = Some(pX);
        evs = Start(psid_of_sdata(proj mStarted.[i]))::evs;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var y : Esk;
      var y' : Eexp;
      var pY : Epk;
      var r : Epk option = None; 
      if (   cSession < qSession && in_dom A mSk && in_dom B mSk
          && !in_dom i mStarted && !in_dom i mCompleted) {
        cSession = cSession + 1;
        y  = $sample_Esk;
        y' = h1(proj (mSk.[B]),y);
        pY = gen_epk(y');
        mStarted.[i] = (B,A,y,y',resp);
        mCompleted.[i] = X;
        r = Some(pY);
        evs = Accept(sid_of_sdata (proj mStarted.[i]) X)::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted) {
        mCompleted.[i] = Y;
        evs = Accept(sid_of_sdata(proj mStarted.[i]) Y)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun ephemeralRev(i : Sidx) : Esk option = {
      var r : Esk option = None;
      if (in_dom i mStarted) {
        r = Some(sd_esk(proj mStarted.[i]));
        evs = EphemeralRev(psid_of_sdata(proj mStarted.[i]))::evs;
      }
      return r;
    }

    fun computeKey(i : Sidx) : Key option = {
      var rv : Key option = None;
      var a, b : Agent;
      var r : Role;
      var x' : Eexp;
      var x : Esk;
      var key : Key;
      if (in_dom i mCompleted) {
        (a,b,x,x',r) = proj mStarted.[i];
        key = h2(gen_sstring x' (proj mSk.[a]) b (proj mCompleted.[i]) r);
        rv = Some key;
      }
      return rv;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      var s : Sid;
      if (in_dom i mCompleted) {
        s = sid_of_sdata (proj mStarted.[i]) (proj mCompleted.[i]);
        evs = SessionRev(sid_of_sdata(proj mStarted.[i]) (proj mCompleted.[i]))::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool;
    var pks : Pk list = [];
    var t_idx : Sidx;
    var key : Key;
    var keyo : Key option;
    var b' : bool = false;
    var i : int = 0;
    var ska : Sk;
    var pka : Pk;

    mSk = Map.empty;
    while (i < qAgent) {
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    } 
    cSession = 0;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    evs = [];
    test = None;

    t_idx = A.choose(pks);
    b = ${0,1};
    if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None) {
      test = Some (sid_of_sdata (proj mStarted.[t_idx]) (proj mCompleted.[t_idx]));
        (* the if-condition implies "mem (Accept (proj O.test)) O.evs" *)
      if (b) {
        keyo = O.computeKey(t_idx);
      } else {
        key  = $sample_Key;
        keyo = Some key;
      }
      b' = A.guess(keyo);
    }
    return (b = b');
  }
}.


pred test_fresh(t : Sid option, evs : Event list) =
  t <> None /\ fresh (proj t) evs.

(*{ Explain security notion *)
section.
  (* For an arbitrary adversary A, *)
  declare module A : Adv.

  (* we want to a find (small) bound eps *)
  const eps : real.

  (* such that the advantage of the adversary is upper bounded by eps. *)
  axiom Secure:
    forall &m,
      2%r * Pr[   AKE(A).main() @ &m : res /\ test_fresh AKE.test AKE.evs] - 1%r < eps.
end section.
(*} end: Explain security notion *)

(*} end: Initial game and security definition *)

lemma Eq_G0_G0_1_1:
  forall (A <: Adv),
    equiv[  AKE(A).main ~ G0_1_0(A).main
          : true ==> ={res} /\ (test_fresh AKE.test AKE.evs){1} = 
                               (test_fresh G0_1_0.test G0_1_0.evs){2}].
proof strict.
  intros=> A.
  fun. inline RO_H1.LRO.init.
  swap {1} 9 7. swap {2} 9 7.
  seq 6 6:
    (={pks,b',i} /\
     AKE.mSk{1} = G0_1.mSk{2} /\
     AKE.cSession{1} = G0_1.cSession{1}).
(*     AKE.cH1{1} = G0_1.cH1{2} /\
     AKE.cH2{1} = G0_1.cH2{2} /\
   (*  AKE.mH1{1} = RO_H1.LRO.m{2} /\ *)
     AKE.sH1{1} = G0_1.sH1{2} /\
     AKE.mH2{1} = G0_1.mH2{2} /\
     AKE.sH2{1} = G0_1.sH2{2} /\
     AKE.mStarted{1} = G0_1.mStarted{2} /\
     AKE.mCompleted{1} =  G0_1.mCompleted{2} /\
     AKE.evs{1} = G0_1.evs{2} /\
     AKE.test{1} = G0_1.test{2}
*)
  eqobs_in. admit.

