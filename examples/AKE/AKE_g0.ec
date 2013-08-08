require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.

require import AKE_defs.

(* The initial module, we keep it simple and inline the
   definitions of h1 and h2 *)
module AKE(FA : Adv) = {
  
  var evs  : Event list               (* events capturing queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mStarted   : (Sidx, Sdata) map  (* map of started initiator session *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  
  module O : AKE_Oracles= {

    fun h2(sstring : Sstring) : Key = {
      var ke : Key;
      ke = $sample_Key;
      if (!in_dom sstring mH2) {
        mH2.[sstring] = ke;
      }
      return Option.proj ((mH2.[sstring]));
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

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
        cH1 = cH1 + 1;
        mH1.[(a,x)] = e;
      } 
      return proj (mH1.[(a,x)]);
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
      var xepk : Epk;
      var a, b : Agent;
      var r : Role;
      var x' : Eexp;
      var xesk : Esk;
      var key : Key;
      if (in_dom i mCompleted) {
        (a,b,xesk,x',r) = proj mStarted.[i];
        key  = h2(gen_sstring x' (proj mSk.[a]) b (proj mCompleted.[i]) r);
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
    mSk = Map.empty;
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
