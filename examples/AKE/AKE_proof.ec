require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.
require import Real.
require import Pair.

require import AKE_defs.

(*{ AKE: Initial game and security definition *)

(* The initial module: we keep it simple and inline the
   definitions of h1 and h2. *)
module AKE(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mStarted   : (Sidx, Sdata) map  (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  
  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
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
      var pX : Epk;
      var x : Esk;
      var x' : Eexp;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
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
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
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
      var r : Key option = None;
      var a, b : Agent;
      var ro : Role;
      var x' : Eexp;
      var x : Esk;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted) {
        (a,b,x,x',ro) = proj mStarted.[i];
        k = h2(gen_sstring x' (proj mSk.[a]) b (proj mCompleted.[i]) ro);
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted) {
        evs = SessionRev(sid_of_sdata(proj mStarted.[i]) (proj mCompleted.[i]))::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;

    init();

    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    } 

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
  (* We want to a find (small) bound eps *)
  const eps : real.

  (* such that the advantage of an adversary is upper bounded by eps. *)
  axiom Secure:
    forall (A <: Adv) &m,
      2%r * Pr[   AKE(A).main() @ &m : res /\ test_fresh AKE.test AKE.evs] - 1%r < eps.
end section.
(*} end: Explain security notion *)

(*} end: Initial game and security definition *)

(*{ First reduction: AKE_EexpRev (replace H1_A by EexpRev oracle) *)

module type AKE_Oracles2 = {
  fun eexpRev(i : Sidx, a : Sk) : Eexp option
  fun h2_a(sstring : Sstring) : Key option
  fun init1(i : Sidx, A : Agent, B : Agent) : Epk option
  fun init2(i : Sidx, Y : Epk) : unit
  fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option
  fun staticRev(A : Agent) : Sk option
  fun sessionRev(i : Sidx) : Key option
}.

module type Adv2 (O : AKE_Oracles2) = {
  fun choose(s : Pk list) : Sidx {*}
  fun guess(k : Key option) : bool
}.

type Sdata2 = (Agent * Agent * Role).

op sd2_actor(sd : Sdata2) = let (A,B,r) = sd in A.
op sd2_peer(sd : Sdata2)  = let (A,B,r) = sd in B.
op sd2_role(sd : Sdata2)  = let (A,B,r) = sd in r.

op compute_sid(mStarted : (Sidx, Sdata2) map) (mEexp : (Sidx, Eexp) map)
              (mCompleted : (Sidx, Epk) map) (i : Sidx) : Sid =
  let sd = proj mStarted.[i] in
  (sd2_actor sd,sd2_peer sd,gen_epk(proj mEexp.[i]),proj mCompleted.[i],sd2_role sd).

op compute_psid(mStarted : (Sidx, Sdata2) map) (mEexp : (Sidx, Eexp) map)
               (i : Sidx) : Psid =
  let sd = proj mStarted.[i] in
  (sd2_actor sd, sd2_peer sd, gen_epk(proj mEexp.[i]), sd2_role sd).

module AKE_EexpRev(FA : Adv2) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
    
  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles2 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
        if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
          r = mEexp.[i];
        }
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
      var pX : Epk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        pX = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (A,B,init);
        evs = Start((A,B,pX,init))::evs;
        r = Some(pX);
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var pY : Epk;
      var r : Epk option = None;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        pY = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        evs = Accept((B,A,pY,X,resp))::evs;
        r = Some(pY);
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
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

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var a : Agent;
      var b : Agent;
      var ro : Role;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted) {
        (a,b,ro) = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[a]) b (proj mCompleted.[i]) ro);
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted) {
        evs = SessionRev(compute_sid mStarted mEexp mCompleted i)::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    var xa' : Eexp = def;
    
    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      xa' = $sample_Eexp;
      mEexp.[sidx] = xa';
    } 


    t_idx = A.choose(pks);
    b = ${0,1};
    if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
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

pred collision_eexp_eexp(m : (Sidx, Eexp) map) =
  exists i j, in_dom i m /\ m.[i] = m.[j] /\ i <> j.

pred collision_eexp_rcvd(evs : Event list) =
  exists (i : int) (j : int) s1 s2 s3,
     i < j /\  nth evs i = Some (Accept s1) /\
     (   (nth evs j  = Some (Start s2)  /\ psid_sent s2 = sid_rcvd s1)
      \/ (nth evs j  = Some (Accept s3) /\ sid_sent s3 = sid_rcvd s1)).

section.
  (* At this point, we still have to show the following: *)
  axiom Remaining_obligation:
    forall (A <: Adv2) &m,
      2%r * Pr[ AKE_EexpRev(A).main() @ &m : res
                    /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs) ]
      - 1%r < eps.
end section.

(*} *)

(*{ Proof: Pr[ AKE : win ] <= eps + Pr[ AKE_EexpRev : win ] *)

section.

declare module A : Adv{ AKE, AKE_EexpRev }.

axiom A_Lossless_choose : 
  forall (O <: AKE_Oracles{A}),
    islossless O.h1_a =>
    islossless O.h2_a =>
    islossless O.init1 =>
    islossless O.init2 =>
    islossless O.resp =>
    islossless O.staticRev =>
    islossless O.ephemeralRev =>
    islossless O.sessionRev =>
    islossless A(O).choose.

axiom A_Lossless_guess : 
  forall (O <: AKE_Oracles{A}),
    islossless O.h1_a =>
    islossless O.h2_a =>
    islossless O.init1 =>
    islossless O.init2 =>
    islossless O.resp =>
    islossless O.staticRev =>
    islossless O.ephemeralRev =>
    islossless O.sessionRev =>
    islossless A(O).guess.

(* Split mStarted into three maps. *)
local
module AKE_1(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEsk       : (Sidx, Esk) map    (* map for ephemeral secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mEsk = Map.empty;
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
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
      var pX : Epk;
      var x : Esk;
      var r : Epk option = None;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        x = $sample_Esk;
        mEsk.[i] = x;
        mEexp.[i] = h1(proj (mSk.[A]),x);
        pX = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (A,B,init);
        r = Some(pX);
        evs = Start(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var y : Esk;
      var pY : Epk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        y  = $sample_Esk;
        mEsk.[i] = y;
        mEexp.[i] = h1(proj (mSk.[B]),y);
        pY = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        r = Some(pY);
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
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
      if (in_dom i mStarted && in_dom i mEexp) {
        r = mEsk.[i];
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var sd : Sdata2;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        sd = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd));
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        evs = SessionRev(compute_sid mStarted mEexp mCompleted i)::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;

    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    } 

    t_idx = A.choose(pks);
    b = ${0,1};
    if (in_dom t_idx mStarted && in_dom t_idx mCompleted && in_dom t_idx mEexp) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
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

(*{ Definitions required for relational invariant between AKE_1 and AKE_2 *)

(* we don't use the predicate because we cannot prevent automatic unfolding *)
op eq_map_split : (Sidx, Sdata)  map ->
                  (Sidx, Sdata2) map ->
                  (Sidx, Esk)    map ->
                  (Sidx, Eexp)   map ->
                  bool.

axiom nosmt eq_map_split_def
  (mStarted1 : (Sidx, Sdata)  map) 
  (mStarted2 : (Sidx, Sdata2) map) 
  (mEsk      : (Sidx, Esk)    map)
  (mEexp     : (Sidx, Eexp)   map):
        eq_map_split mStarted1 mStarted2 mEsk mEexp
   = (    dom mStarted1 = dom mStarted2 /\ dom mStarted2 = dom mEsk
      /\ dom mStarted2 = dom mEexp /\
      (forall (i : Sidx) (sd1 : Sdata) (A B : Agent) (r : Role),
         in_dom i mStarted1 =>
         sd_actor (proj mStarted1.[i]) = sd2_actor (proj mStarted2.[i]) /\
         sd_peer  (proj mStarted1.[i]) = sd2_peer  (proj mStarted2.[i]) /\
         sd_role  (proj mStarted1.[i]) = sd2_role  (proj mStarted2.[i]) /\
         sd_esk   (proj mStarted1.[i]) = proj mEsk.[i] /\
         sd_eexp  (proj mStarted1.[i]) = proj mEexp.[i])).

lemma eq_map_split_1(mStarted1 : (Sidx, Sdata)  map)
                    (mStarted2 : (Sidx, Sdata2) map)
                    (mEsk      : (Sidx, Esk)    map) 
                    (mEexp     : (Sidx, Eexp)   map)
                    (i : Sidx):
     in_dom i mStarted1
  => eq_map_split mStarted1 mStarted2 mEsk mEexp
  => psid_of_sdata (proj mStarted1.[i]) = compute_psid mStarted2 mEexp i.
proof strict.
  rewrite /psid_of_sdata /compute_psid eq_map_split_def.
  elim /tuple5_ind (proj mStarted1.[i]).
  smt.
qed.

lemma eq_map_split_2(mStarted1  : (Sidx, Sdata)  map)
                    (mStarted2  : (Sidx, Sdata2) map)
                    (mCompleted : (Sidx, Epk)    map)
                    (mEsk       : (Sidx, Esk) map) 
                    (mEexp      : (Sidx, Eexp) map)
                    (i : Sidx):
     in_dom i mStarted1
  => in_dom i mCompleted
  => eq_map_split mStarted1 mStarted2 mEsk mEexp
  =>   sid_of_sdata (proj mStarted1.[i]) (proj mCompleted.[i])
     = compute_sid mStarted2 mEexp mCompleted i.
proof strict.
  rewrite eq_map_split_def /sid_of_sdata /compute_sid.
  elim /tuple5_ind (proj mStarted1.[i]).
  smt.
qed.

lemma eq_map_split_3(mStarted1  : (Sidx, Sdata)  map)
                    (mStarted2  : (Sidx, Sdata2) map)
                    (mCompleted : (Sidx, Epk)    map)
                    (mEsk       : (Sidx, Esk) map) 
                    (mEexp      : (Sidx, Eexp) map)
                    (i : Sidx):
     eq_map_split mStarted1 mStarted2 mEsk mEexp
  => in_dom i mStarted1 = in_dom i mStarted2.
proof strict.
  by rewrite eq_map_split_def; smt.
qed.

lemma eq_map_split_4(mStarted1  : (Sidx, Sdata)  map)
                    (mStarted2  : (Sidx, Sdata2) map)
                    (mCompleted : (Sidx, Epk)    map)
                    (mEsk       : (Sidx, Esk) map) 
                    (mEexp      : (Sidx, Eexp) map)
                    (i : Sidx):
     eq_map_split mStarted1 mStarted2 mEsk mEexp
  => in_dom i mStarted1 = in_dom i mEexp.
proof strict.
  by rewrite eq_map_split_def; smt.
qed.

(*} end: Definitions required for relational invariant between AKE_1 and AKE_2 *)

(*{ First handle oracles that are unaffected by changes *)

local
lemma Eq_AKE_AKE_1_O_h1:
  equiv[ AKE(A).O.h1 ~ AKE_1(A).O.h1 :
         (AKE.mH1{1} = AKE_1.mH1{2} /\ ={x,a})
         ==> (AKE.mH1{1} = AKE_1.mH1{2} /\ ={res}) ].
proof strict.
  by fun; eqobs_in.
qed.

local
lemma Eq_AKE_AKE_1_O_h2:
  equiv[ AKE(A).O.h2 ~ AKE_1(A).O.h2 :
         (AKE.mH2{1} = AKE_1.mH2{2} /\ ={sstring})
         ==> (AKE.mH2{1} = AKE_1.mH2{2} /\ ={res}) ].
proof strict.
  by fun; eqobs_in.
qed.
  
local
lemma Eq_AKE_AKE_1_O_h2_a:
  equiv[ AKE(A).O.h2_a ~ AKE_1(A).O.h2_a :
         ( ={sstring} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if; [ by smt | | by skip; smt ].
  wp.
  call (Eq_AKE_AKE_1_O_h2).
  wp.
  skip; smt.
qed.

local
lemma Eq_AKE_AKE_1_O_staticRev:
  equiv[ AKE(A).O.staticRev ~ AKE_1(A).O.staticRev :
         ( ={A} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun; wp; skip; smt.
qed.

(*} end: First handle oracles that are unaffected by changes *)

(*{ Then handle oracles that only read the modified maps. *)

local
lemma Eq_AKE_AKE_1_O_init2:
  equiv[ AKE(A).O.init2 ~ AKE_1(A).O.init2 :
          ( ={i,Y} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
          ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  if ; [ by smt | | by skip; smt ].
  by wp; skip; smt.
qed.

local
lemma Eq_AKE_AKE_1_O_ephemeralRev:
  equiv[ AKE(A).O.ephemeralRev ~ AKE_1(A).O.ephemeralRev :
          ( ={i} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
          ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  wp;  skip; intros &1 &2.
  rewrite eq_map_split_def.
  by progress; smt.
qed.

local
lemma Eq_AKE_AKE_1_O_computeKey:
  equiv[ AKE(A).O.computeKey ~ AKE_1(A).O.computeKey :
          ( ={i} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
          ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if ;[ by smt | | by skip; smt ].
  wp.
  call (Eq_AKE_AKE_1_O_h2).
  wp; skip. progress.
    by generalize H; rewrite eq_map_split_def; smt.
    by smt.
qed.

local
lemma Eq_AKE_AKE_1_O_sessionRev:
  equiv[ AKE(A).O.sessionRev ~ AKE_1(A).O.sessionRev :
          ( ={i} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if; [ by smt | | by skip; smt ]. 
  call Eq_AKE_AKE_1_O_computeKey.
  wp; skip. smt.
qed.

local
lemma Eq_AKE_AKE_1_O_h1_a:
  equiv[ AKE(A).O.h1_a ~ AKE_1(A).O.h1_a :
         ( ={a,x} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if; [ by smt | | by skip; smt ].
  wp.
  call Eq_AKE_AKE_1_O_h1.
  wp; skip; smt.
qed.

(*} end: Then handle oracles that only read the modified maps*)

(*{ Lastly handle oracles that write the modified maps. *)

local
lemma Eq_AKE_AKE_1_O_init1:
  equiv[ AKE(A).O.init1 ~ AKE_1(A).O.init1 :
         ( ={i,A,B} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if; [ by smt | | skip; by smt ].
  wp.
  call Eq_AKE_AKE_1_O_h1.
  wp.
  rnd.
  skip; progress. smt. smt. smt. 
  generalize H.
  rewrite !eq_map_split_def. progress. smt. smt. smt. smt. smt.
  case (i{2} = i0).
    intros eq. rewrite !eq !get_setE; smt.
  intros neq. rewrite !get_setNE. smt. smt. 
    generalize H9.
    rewrite (in_dom_setNE i0 AKE.mStarted{1}). smt. smt.
  smt.
  smt.
qed.

local
lemma Eq_AKE_AKE_1_O_resp:
  equiv[ AKE(A).O.resp ~ AKE_1(A).O.resp :
         ( ={i, B, A, X} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2})
         ==>
         ( ={res} /\
           AKE.evs{1}         = AKE_1.evs{2} /\
           AKE.test{1}        = AKE_1.test{2} /\
           AKE.cH1{1}         = AKE_1.cH1{2} /\
           AKE.cH2{1}         = AKE_1.cH2{2} /\
           AKE.mH1{1}         = AKE_1.mH1{2} /\
           AKE.sH1{1}         = AKE_1.sH1{2} /\
           AKE.mH2{1}         = AKE_1.mH2{2} /\
           AKE.sH2{1}         = AKE_1.sH2{2} /\
           AKE.mSk{1}         = AKE_1.mSk{2} /\
           AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
           eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                        AKE_1.mEsk{2} AKE_1.mEexp{2}) ].
proof strict.
  fun.
  sp.
  if; [ by smt | | skip; by smt ].
  wp.
  call Eq_AKE_AKE_1_O_h1.
  wp.
  rnd; skip; progress. smt. smt. smt.
  generalize H. rewrite !eq_map_split_def.
  progress.
    smt. smt. smt. smt. smt.
  case (i{2} = i0).
    intros eq. rewrite !eq !get_setE; smt.
  intros neq. rewrite !get_setNE. smt. smt.
    generalize H10.
    rewrite (in_dom_setNE i0 AKE.mStarted{1}). smt. smt.
  smt.
  smt.
qed.

(*} end: Lastly handle oracles that write the modified maps. *)

local
lemma Eq_AKE_AKE_1:
  equiv[ AKE(A).main ~ AKE_1(A).main : true ==>
            (res /\ test_fresh AKE.test AKE.evs){1}
         => (res /\ test_fresh AKE_1.test AKE_1.evs){2} ].
proof strict.
  fun.
  inline AKE(A).init AKE_1(A).init.
  seq 20 22:
    ( ={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2}).
  by wp; skip; rewrite eq_map_split_def; smt.
  seq 1 1:
    ( ={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2}).
  while 
    ( ={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2}).  
  by wp; rnd; wp; skip; smt.
  by skip; smt.
  seq 1 1:
    ( ={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2} /\
      ={glob A}).
  call 
     (_: 
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2}).
    apply Eq_AKE_AKE_1_O_h1_a.
    apply Eq_AKE_AKE_1_O_h2_a.
    apply Eq_AKE_AKE_1_O_init1.
    apply Eq_AKE_AKE_1_O_init2.
    apply Eq_AKE_AKE_1_O_resp.
    apply Eq_AKE_AKE_1_O_staticRev.
    apply Eq_AKE_AKE_1_O_ephemeralRev.
    apply Eq_AKE_AKE_1_O_sessionRev.
    by skip; smt.
    seq 1 1:
    ( ={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2} /\
      ={glob A}).
    by rnd; skip; smt.
    if; [ by smt | | by skip; smt ].
    call 
     (_: 
      AKE.evs{1}         = AKE_1.evs{2} /\
      AKE.test{1}        = AKE_1.test{2} /\
      AKE.cH1{1}         = AKE_1.cH1{2} /\
      AKE.cH2{1}         = AKE_1.cH2{2} /\
      AKE.mH1{1}         = AKE_1.mH1{2} /\
      AKE.sH1{1}         = AKE_1.sH1{2} /\
      AKE.mH2{1}         = AKE_1.mH2{2} /\
      AKE.sH2{1}         = AKE_1.sH2{2} /\
      AKE.mSk{1}         = AKE_1.mSk{2} /\
      AKE.mCompleted{1}  = AKE_1.mCompleted{2} /\
      eq_map_split AKE.mStarted{1} AKE_1.mStarted{2}
                   AKE_1.mEsk{2} AKE_1.mEexp{2}).
    apply Eq_AKE_AKE_1_O_h1_a.
    apply Eq_AKE_AKE_1_O_h2_a.
    apply Eq_AKE_AKE_1_O_init1.
    apply Eq_AKE_AKE_1_O_init2.
    apply Eq_AKE_AKE_1_O_resp.
    apply Eq_AKE_AKE_1_O_staticRev.
    apply Eq_AKE_AKE_1_O_ephemeralRev.
    apply Eq_AKE_AKE_1_O_sessionRev.
    sp.
    if; first by smt.
    call Eq_AKE_AKE_1_O_computeKey.
    by skip; progress; smt.
    by wp; rnd; skip; progress; smt.
qed.

(* Move sampling of ephemeral exponents to loop in main.
   Can be justified with the lazy/eager RO transformation.
*)
local
module AKE_2(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEsk       : (Sidx, Esk) map    (* map for ephemeral secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mEsk = Map.empty;
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
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
      var pX : Epk;
      var x : Esk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        x = proj mEsk.[i];
        mEexp.[i] = h1(proj (mSk.[A]),x);
        pX = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (A,B,init);
        r = Some(pX);
        evs = Start(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var y : Esk;
      var pY : Epk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        y = proj mEsk.[i];
        mEexp.[i] = h1(proj (mSk.[B]),y);
        pY = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        r = Some(pY);
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
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
      if (in_dom i mStarted && in_dom i mEexp) {
        r = mEsk.[i];
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var sd : Sdata2;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        sd = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd));
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        evs = SessionRev(compute_sid mStarted mEexp mCompleted i)::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx = def;
    var ska : Sk = def;
    var pka : Pk = def;

    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      mEsk.[sidx] = $sample_Esk;
    } 

    t_idx = A.choose(pks);
    b = ${0,1};
    if (in_dom t_idx mStarted && in_dom t_idx mCompleted && in_dom t_idx mEexp) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
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

local
lemma Eq_AKE_1_AKE_2:
  equiv[ AKE_1(A).main ~ AKE_2(A).main : true ==>
            (res /\ test_fresh AKE_1.test AKE_1.evs){1}
         => (res /\ test_fresh AKE_2.test AKE_2.evs){2} ].
proof strict.
  admit. (* Lazy to eager random oracle *)
qed.

op bad_esk_col_op : (Sidx, Esk) map -> bool.

op sidx_to_int: Sidx -> int.
axiom sidx_to_int_inj(i : Sidx) (j : Sidx):
  sidx_to_int i = sidx_to_int j => i = j.

axiom bad_esk_col_op_def(mEsk : (Sidx, Esk) map):
    bad_esk_col_op mEsk =
    (exists i j,    sidx_to_int i < sidx_to_int j
                 /\ mEsk.[i] <> None /\ mEsk.[i] = mEsk.[j]).

op bad_esk_norev_op : (Sidx, Esk) map -> (Sidx, Sdata2) map
     -> (Sidx, Eexp) map -> Esk -> Event list -> bool.

axiom bad_esk_norev_op_def(mEsk : (Sidx, Esk) map)
                          (mStarted : (Sidx, Sdata2) map)
                          (mEexp : (Sidx, Eexp) map)
                          (x : Esk)
                          (evs : Event list):
  bad_esk_norev_op mEsk mStarted mEexp x evs =
  (exists i,
     mEsk.[i] = Some x /\
     ! (mem (EphemeralRev (compute_psid mStarted mEexp i)) evs)).

(* Add bad flags bad_esk_col and bad_esk_guess *)
local
module AKE_3(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH1 : ((Sk * Esk), Eexp) map    (* map for h1 *)
  var sH1 : (Sk * Esk) set            (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEsk       : (Sidx, Esk) map    (* map for ephemeral secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  var bad_esk_col : bool              (* esk collision *)
    (* There are two session indexes with the same ephemeral key. *)

  var bad_esk_norev : bool            (* h1_a query without previous reveal *)
    (* There is a h1_a(x,_) query such that Ex i. mEsk[i] = Some x and no EphemeralRev for i *)

  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mEsk = Map.empty;
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_esk_col = false;
    bad_esk_norev = false;
  }

  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
        mH1.[(a,x)] = e;
      } 
      return proj mH1.[(a,x)];
    }

    fun h1_a(a : Sk, x : Esk) : Eexp option = {
      var r : Eexp option = None;
      var xe : Eexp;
      if (bad_esk_norev_op mEsk mStarted mEexp x evs)
        bad_esk_norev = true;
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
      var pX : Epk;
      var x : Esk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        x = proj mEsk.[i];
        mEexp.[i] = h1(proj (mSk.[A]),x);
        pX = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (A,B,init);
        r = Some(pX);
        evs = Start(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var y : Esk;
      var pY : Epk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        y = proj mEsk.[i];
        mEexp.[i] = h1(proj (mSk.[B]),y);
        pY = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        r = Some(pY);
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
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
      if (in_dom i mStarted && in_dom i mEexp) {
        r = mEsk.[i];
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var sd : Sdata2;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        sd = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd));
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        evs = SessionRev(compute_sid mStarted mEexp mCompleted i)::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx = def;
    var ska : Sk = def;
    var pka : Pk = def;

    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      mEsk.[sidx] = $sample_Esk;
    } 

    if (bad_esk_col_op mEsk) bad_esk_col = true;
    
    t_idx = A.choose(pks);
    b = ${0,1};
    if (in_dom t_idx mStarted && in_dom t_idx mCompleted && in_dom t_idx mEexp) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
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

local
lemma Eq_AKE_2_AKE_3:
  equiv[ AKE_2(A).main ~ AKE_3(A).main : true ==>
            (res /\ test_fresh AKE_2.test AKE_2.evs){1}
         => (res /\ test_fresh AKE_3.test AKE_3.evs){2} ].
proof strict.
  admit. (* We just added some ghost state and ghost code for setting bad. *)
qed.

(*{ Proof: Bound probability of bad_esk_col *)

op bad_esk_col_x_op : (Sidx, Esk) map -> Esk -> bool.

axiom bad_esk_col_x_op_def(mEsk : (Sidx, Esk) map) (x : Esk):
  bad_esk_col_x_op mEsk x = (exists i, mEsk.[i] = Some x).

(* Minimal game to bound probability *)
local
module AKE_3_1(FA : Adv) = {
  var mEsk : (Sidx, Esk) map    (* map for ephemeral secret keys *)

  fun main() : bool = {
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx = def;
    var x : Esk = def;
    var bad_esk_col : bool = false;
 
    mEsk = Map.empty;

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      x = $sample_Esk;
      if (bad_esk_col_x_op mEsk x) bad_esk_col = true;
      mEsk.[sidx] = x;
    }

    return bad_esk_col;
  }
}.

lemma bad_esk_col_x_op_imp_bad_esk_col_op(mEsk : (Sidx, Esk) map) (i : Sidx) (x : Esk) :
  mEsk.[i] = None => bad_esk_col_x_op mEsk x => bad_esk_col_op mEsk.[i <- x].
proof strict.
  intros=> H_i_none.
  rewrite !bad_esk_col_op_def bad_esk_col_x_op_def.
  intros=> Hex; elim Hex; intros=> i0 Hi0_some.
  case (sidx_to_int i < sidx_to_int i0). intros=> less.
    exists i. exists i0. smt.
  intros=> not_less.
  exists i0. exists i. smt.
qed.

lemma not_bad_esk_col_x_imp_not_update(mEsk : (Sidx, Esk) map) (i : Sidx) (x : Esk) :
  mEsk.[i] = None =>
  ! bad_esk_col_x_op mEsk x =>
  bad_esk_col_op mEsk.[i <- x] = bad_esk_col_op mEsk.
proof strict.
  intros=> H_i_none.
  rewrite !bad_esk_col_op_def bad_esk_col_x_op_def.
  intros=> Hnex.
  rewrite rw_eq_iff.
  apply iffI.
  intros=> Hex; elim Hex; intros a b [Hneq] [Hsome] Heq.
  case (a = i). intros=> eq_a_i.
    case (b = i). intros=> eq_b_i.
       generalize Hsome Heq.
       rewrite !eq_a_i !eq_b_i !get_setE. smt.
    intros=> neq_b_i. generalize Hsome Heq. rewrite !eq_a_i !get_setE !get_setNE; smt.
  intros=> neq_a_i.
  case (b = i). intros=> eq_b_i.
    generalize Hsome Heq. rewrite !eq_b_i !get_setE !get_setNE. smt. smt.
  intros=> neq_b_i. generalize Hsome Heq. rewrite !get_setNE. smt. smt. smt.
  intros=> Hex; elim Hex; intros a b [Hneq] [Hsome] Heq.
  case (sidx_to_int a < sidx_to_int b). intros=> less.
  exists a. exists b. split; first trivial.
  case (a = i). intros=> eq_a_i.
    case (b = i). intros=> eq_b_i.
       rewrite !eq_a_i !eq_b_i !get_setE. smt.
    intros=> neq_b_i. rewrite !eq_a_i !get_setE !get_setNE; smt.
  intros=> neq_a_i.
  case (b = i). intros=> eq_b_i.
    rewrite !eq_b_i !get_setE !get_setNE. smt. smt.
  intros=> neq_b_i. rewrite !get_setNE. smt. smt. smt.
  intros=> nless.
  exists b. exists a. split; first by smt.
  case (a = i). intros=> eq_a_i.
    case (b = i). intros=> eq_b_i.
       rewrite !eq_a_i !eq_b_i !get_setE. smt.
    intros=> neq_b_i. rewrite !eq_a_i !get_setE !get_setNE; smt.
  intros=> neq_a_i.
  case (b = i). intros=> eq_b_i.
    rewrite !eq_b_i !get_setE !get_setNE. smt. smt.
  intros=> neq_b_i. rewrite !get_setNE. smt. smt. smt.
qed.

local lemma bad_AKE_3_O_h1_a:
  bd_hoare[ AKE_3(A).O.h1_a : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. wp. sp. inline AKE_3(A).O.h1. wp. sp. rnd.
  rewrite -/cpTrue -/(Distr.weight sample_Eexp). skip; smt.
  skip; smt. 
qed.

local lemma bad_AKE_3_O_h2_a:
  bd_hoare[ AKE_3(A).O.h2_a : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. wp. sp. inline AKE_3(A).O.h2. wp. sp. rnd.
  rewrite -/cpTrue -/(Distr.weight sample_Eexp). skip; smt.
  skip; smt.
qed.

local lemma bad_AKE_3_O_init2:
  bd_hoare[ AKE_3(A).O.init2 : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma bad_AKE_3_O_ephemeralRev:
  bd_hoare[ AKE_3(A).O.ephemeralRev : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma bad_AKE_3_O_staticRev:
  bd_hoare[ AKE_3(A).O.staticRev : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma bad_AKE_3_O_sessionRev:
  bd_hoare[ AKE_3(A).O.sessionRev : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.computeKey.
  sp. if. inline AKE_3(A).O.h2. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by wp; skip; smt.
  by skip; smt.
qed.

local lemma bad_AKE_3_O_init1:
  bd_hoare[ AKE_3(A).O.init1 : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.h1. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by skip; smt.
qed.

local lemma bad_AKE_3_O_resp:
  bd_hoare[ AKE_3(A).O.resp : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.h1. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by skip; smt.
qed.

(* FIXME: we would like to prove that bad_esk_col is preserved *)
local lemma not_bad_AKE_3_O_h1_a:
  bd_hoare[ AKE_3(A).O.h1_a : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. wp. sp. inline AKE_3(A).O.h1. wp. sp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by skip; smt.
qed.

local lemma not_bad_AKE_3_O_h2_a:
  bd_hoare[ AKE_3(A).O.h2_a : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. wp. sp. inline AKE_3(A).O.h2. wp. sp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp) ; skip; smt.
  by skip; smt.
qed.

local lemma not_bad_AKE_3_O_init2:
  bd_hoare[ AKE_3(A).O.init2 : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma not_bad_AKE_3_O_ephemeralRev:
  bd_hoare[ AKE_3(A).O.ephemeralRev : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma not_bad_AKE_3_O_staticRev:
  bd_hoare[ AKE_3(A).O.staticRev : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. wp. skip; smt.
qed.

local lemma not_bad_AKE_3_O_sessionRev:
  bd_hoare[ AKE_3(A).O.sessionRev : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.computeKey.
  sp. if. inline AKE_3(A).O.h2. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by wp; skip; smt.
  by skip; smt.
qed.

local lemma not_bad_AKE_3_O_init1:
  bd_hoare[ AKE_3(A).O.init1 : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.h1. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by skip; smt.
qed.

local lemma not_bad_AKE_3_O_resp:
  bd_hoare[ AKE_3(A).O.resp : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col] = 1%r.
proof strict.
  fun. sp. if. inline AKE_3(A).O.h1. sp. wp. rnd.
  by rewrite -/cpTrue -/(Distr.weight sample_Eexp); skip; smt.
  by skip; smt.
qed.

local
lemma Eq_AKE_3_AKE_3_1_bad_esk_col:
  equiv[ AKE_3(A).main ~ AKE_3_1(A).main : true ==>
            AKE_3.bad_esk_col{1} => res{2} ].
proof strict.
  fun.
  seq 12 5:
    (   ((bad_esk_col_op AKE_3.mEsk){1} = bad_esk_col{2})
     /\ AKE_3.bad_esk_col{1} = false
     /\ sidx{1} = sidx{2}
     /\ sidxs{1} = sidxs{2}
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}
     /\ AKE_3.mEsk{1} = Map.empty
    ).
  inline AKE_3(A).init.
  wp; skip; smt.
  seq 1 0:
    (   ((bad_esk_col_op AKE_3.mEsk){1} = bad_esk_col{2})
     /\ AKE_3.bad_esk_col{1} = false
     /\ sidx{1} = sidx{2}
     /\ sidxs{1} = sidxs{2}
     /\ AKE_3.mEsk{1} = Map.empty
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}
     ).
  while {1}
    (   ((bad_esk_col_op AKE_3.mEsk){1} = bad_esk_col{2})
     /\ AKE_3.bad_esk_col{1} = false
     /\ sidx{1} = sidx{2}
     /\ AKE_3.mEsk{1} = Map.empty
     /\ sidxs{1} = sidxs{2}
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}) (qAgent - i{1}).
    progress.
    wp.
    rnd.
    wp.
      by skip; smt.
      by skip; smt.
  seq 1 1:
    (   ((bad_esk_col_op AKE_3.mEsk){1} = bad_esk_col{2})
     /\ AKE_3.bad_esk_col{1} = false
     /\ sidx{1} = sidx{2}
     /\ sidxs{1} = sidxs{2}
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}).
  while
    (   ((bad_esk_col_op AKE_3.mEsk){1} = bad_esk_col{2})
     /\ AKE_3.bad_esk_col{1} = false
     /\ sidx{1} = sidx{2}
     /\ sidxs{1} = sidxs{2}
     /\ (forall i, mem i sidxs{1} => AKE_3.mEsk.[i]{1} = None)
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}).
  wp. rnd. wp.
  skip. progress. smt.
    apply eqT. apply bad_esk_col_x_op_imp_bad_esk_col_op. smt. smt. smt.
    apply not_bad_esk_col_x_imp_not_update. smt. smt. smt.
  skip. smt.
  seq 1 0:
    (   (AKE_3.bad_esk_col{1} = bad_esk_col{2})
     /\ sidx{1} = sidx{2}
     /\ sidxs{1} = sidxs{2}
     /\ AKE_3.mEsk{1} = AKE_3_1.mEsk{2}).
    wp; skip; smt.
  seq 1 0 : (AKE_3.bad_esk_col{1} = bad_esk_col{2}).
  case AKE_3.bad_esk_col{1}.
    call {1}  (_ : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col).
      fun (AKE_3.bad_esk_col) => //.
      by apply A_Lossless_choose.
      by apply bad_AKE_3_O_h1_a.
      by apply bad_AKE_3_O_h2_a.
      by apply bad_AKE_3_O_init1.
      by apply bad_AKE_3_O_init2.
      by apply bad_AKE_3_O_resp.
      by apply bad_AKE_3_O_staticRev.
      by apply bad_AKE_3_O_ephemeralRev.
      by apply bad_AKE_3_O_sessionRev.
      skip; smt.
  call {1}  (_ : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col).
    fun (!AKE_3.bad_esk_col) => //.
    by apply A_Lossless_choose.
    by apply not_bad_AKE_3_O_h1_a.
    by apply not_bad_AKE_3_O_h2_a.
    by apply not_bad_AKE_3_O_init1.
    by apply not_bad_AKE_3_O_init2.
    by apply not_bad_AKE_3_O_resp.
    by apply not_bad_AKE_3_O_staticRev.
    by apply not_bad_AKE_3_O_ephemeralRev.
    by apply not_bad_AKE_3_O_sessionRev.
    skip; smt.
  seq 1 0 : (AKE_3.bad_esk_col{1} = bad_esk_col{2}).
  by rnd {1}; skip; smt.
  if {1}; [ | by skip; smt ].
    seq 2 0 : (AKE_3.bad_esk_col{1} = bad_esk_col{2}).
      sp. if {1}. inline AKE_3(A).O.computeKey. sp. if {1}. wp. inline AKE_3(A).O.h2.
      sp. wp. rnd {1}. skip. progress.
      rewrite -/cpTrue -/(Distr.weight sample_Key); smt. wp; skip; smt.
      wp; rnd {1}. rewrite -/cpTrue -/(Distr.weight sample_Key); skip; smt.
    case AKE_3.bad_esk_col{1}.
      call {1}  (_ : AKE_3.bad_esk_col ==> AKE_3.bad_esk_col).
      fun (AKE_3.bad_esk_col) => //.
      by apply A_Lossless_guess.
      by apply bad_AKE_3_O_h1_a.
      by apply bad_AKE_3_O_h2_a.
      by apply bad_AKE_3_O_init1.
      by apply bad_AKE_3_O_init2.
      by apply bad_AKE_3_O_resp.
      by apply bad_AKE_3_O_staticRev.
      by apply bad_AKE_3_O_ephemeralRev.
      by apply bad_AKE_3_O_sessionRev.
      skip; smt.
    call {1}  (_ : !AKE_3.bad_esk_col ==> !AKE_3.bad_esk_col).
      fun (!AKE_3.bad_esk_col) => //.
      by apply A_Lossless_guess.
      by apply not_bad_AKE_3_O_h1_a.
      by apply not_bad_AKE_3_O_h2_a.
      by apply not_bad_AKE_3_O_init1.
      by apply not_bad_AKE_3_O_init2.
      by apply not_bad_AKE_3_O_resp.
      by apply not_bad_AKE_3_O_staticRev.
      by apply not_bad_AKE_3_O_ephemeralRev.
      by apply not_bad_AKE_3_O_sessionRev.
      skip; smt.
qed.

(* Call function in loop body so that we can use FEL.
   Also remove sidxs and use fdom mEsk directly.
*)
local
module AKE_3_2(FA : Adv) = {
  var mEsk : (Sidx, Esk) map    (* map for ephemeral secret keys *)
  var bad_esk_col : bool

  fun sample() : unit = {
    var x : Esk;
    var sidx : Sidx;
    if (fdom mEsk <> univ_Sidx) {
      sidx = pick (filter (lambda x, ! mem x (fdom mEsk)) univ_Sidx);
      x = $sample_Esk;
      if (!bad_esk_col && bad_esk_col_x_op mEsk x) bad_esk_col = true;
      mEsk.[sidx] = x;
    }
  }

  fun main() : bool = {
    mEsk = Map.empty;
    bad_esk_col = false;

    while (fdom mEsk <> univ_Sidx) {
      sample();
    }

    return bad_esk_col;
  }
}.

local
lemma Eq_AKE_3_1_AKE_3_2_bad_esk_col:
  equiv[ AKE_3_1(A).main ~ AKE_3_2(A).main
         : true ==> res{1} => AKE_3_2.bad_esk_col{2} ].
proof strict.
  fun. inline AKE_3_2(A).sample.
  seq 5 2 :
    (sidxs{1} = filter (lambda x, ! mem x (fdom AKE_3_2.mEsk{2})) univ_Sidx /\
     AKE_3_1.mEsk{1} = AKE_3_2.mEsk{2}  /\
     bad_esk_col{1}  = AKE_3_2.bad_esk_col{2}).
    wp. skip. progress. rewrite fdom_empty.
    cut H: (lambda (x : Sidx), ! mem x FSet.empty) = cpTrue.
    apply fun_ext. rewrite /cpTrue /Fun.(==).
    progress. smt.
    rewrite H. smt.
  while
    (sidxs{1} = filter (lambda x, ! mem x (fdom AKE_3_2.mEsk{2})) univ_Sidx /\
     AKE_3_1.mEsk{1} = AKE_3_2.mEsk{2}  /\
     bad_esk_col{1}  = AKE_3_2.bad_esk_col{2}).
    rcondt {2} 1. progress. skip. smt.
    seq 1 1:
    (sidxs{1} = filter (lambda x, ! mem x (fdom AKE_3_2.mEsk{2})) univ_Sidx /\
     AKE_3_1.mEsk{1} = AKE_3_2.mEsk{2}  /\
     bad_esk_col{1}  = AKE_3_2.bad_esk_col{2} /\
     ={sidx}). wp. skip. smt.
    swap {1} 1 2.
    seq 1 1:
    (sidxs{1} = filter (lambda x, ! mem x (fdom AKE_3_2.mEsk{2})) univ_Sidx /\
     AKE_3_1.mEsk{1} = AKE_3_2.mEsk{2}  /\
     bad_esk_col{1}  = AKE_3_2.bad_esk_col{2} /\
     ={x,sidx}).
    rnd. skip. smt.
    seq 1 1:
    (sidxs{1} = filter (lambda x, ! mem x (fdom AKE_3_2.mEsk{2})) univ_Sidx /\
     AKE_3_1.mEsk{1} = AKE_3_2.mEsk{2}  /\
     bad_esk_col{1}  = AKE_3_2.bad_esk_col{2} /\
     ={x,sidx}).
    wp. skip. smt.
    wp. skip. progress.
      (* sidxs = filter ... mEsk preserved *)
      apply set_ext.
      rewrite /FSet.(==).
      intros=> i.
      case (i = sidx{2}). intros=> H_i_sidx.
        rewrite !H_i_sidx. progress. smt.
        generalize H. 
        rewrite !mem_filter. progress.
        generalize H0. rewrite !mem_fdom. smt.
      intros H_neq. rewrite mem_rm_neq => //.
      rewrite !mem_filter. progress. trivial.
      generalize H0. rewrite !mem_fdom. smt. trivial.
      generalize H0. rewrite mem_fdom. smt.
      (* relation between fdom mEsk = univ and rm (filter ..) .. = empty *)
      apply not_def => Hfd.
      cut Hex:
        exists x,
          mem x
            (rm sidx{2} (filter (lambda x, !mem x (fdom AKE_3_2.mEsk{2})) 
                                univ_Sidx)). smt.
      elim Hex; intros=> z Hmem.
      case (z = sidx{2}). intros=> Heq.
        generalize Hmem. rewrite !Heq !mem_rm !mem_filter. smt.
      intros Hneq. generalize Hmem. rewrite mem_rm_neq // mem_filter.
      beta.
      intros=> [mem_univ] not_mem_dom. smt.
      (* relation between rm (filter ..) .. = empty and fdom mEsk = univ *)
      apply not_def => Hnempty.
      cut Hex: exists z, ! mem z (fdom AKE_3_2.mEsk{2}.[sidx{2} <- x{2}]).
        case (forall z, mem z (fdom AKE_3_2.mEsk{2}.[sidx{2} <- x{2}]));
          last by smt.
        intros=> Hall.
        cut L: fdom AKE_3_2.mEsk{2}.[sidx{2} <- x{2}] = univ_Sidx.
          by apply set_ext; rewrite /FSet.(==); smt.
        smt.
      elim Hex. intros=> z Hnmem.
      generalize Hnmem. rewrite mem_fdom. simplify.
      cut L: forall z,
       !mem z (rm sidx{2}
                  (filter (lambda (x : Sidx), ! mem x (fdom AKE_3_2.mEsk{2}))
                          univ_Sidx)).
      smt.
      cut Hmemz:= L z.
      case (sidx{2} = z). intros Heq. generalize Hmemz.
        rewrite !Heq mem_rm. smt.
      intros=> Hneq. generalize Hmemz.
      rewrite mem_rm mem_filter. progress. smt.
    skip. smt.
qed.

lemma leq_div(x1 y x2 : real):
  y > 0%r => x1 <= x2 => x1 / y <= x2 / y by [].


lemma zero_leq_divr(x y : real):
  x >= 0%r => y > 0%r => 0%r <= x / y.
proof strict.
  progress.
  cut G: 0%r = 0%r / y. smt.
  rewrite G. apply leq_div.
  smt. smt.
qed.


lemma card_leq(X Y : 'a set):
  X <= Y => card X <= card Y.
proof strict.
  case (X = Y). smt.
  progress.
  cut G: card X < card Y. smt.
  smt.
qed.

lemma finite_rng_dom(m : ('a,'b) map):
  ISet.Finite.finite (dom m) => ISet.Finite.finite (rng m).
proof strict.
  admit. (* surjection from dom to rng: lamba x, proj m.[x] *)
qed.

lemma mem_frng(x : 'b) (m : (Sidx,'b) map):
   mem x (frng m) = ISet.mem x (rng m).
proof strict.
  cut Fin: ISet.Finite.finite (rng m); first by smt.
  by rewrite /frng; smt.
qed.

lemma card_frng_fdom(m : ('a,'b) map):
  card (frng m) <= card (fdom m).
proof strict.
  admit. (* surjection from fdom to frng: lamba x, proj m.[x] *)
qed.

lemma filter_bad_esk_col_x(m : (Sidx, Esk) map):
   filter (lambda x, bad_esk_col_x_op m x) univ_Esk <= frng m.
proof strict.
  cut Leq:   (lambda (x : Esk), bad_esk_col_x_op m x)
           = (lambda (x : Esk), exists i, m.[i] = Some x).
    apply fun_ext. rewrite /Fun.(==). progress. smt.
  rewrite Leq /FSet.(<=).
  progress.
  cut Hex: exists i, m.[i] = Some x; first by smt.
  rewrite mem_frng.
  smt.
qed.

lemma leq_real_int(x y : int): x <= y => x%r <= y%r by smt.

lemma int_leq_trans(a b c : int): a <= b => b <= c => a <= c by smt.

lemma dom_set_add(m : (Sidx,'b) map) (x : Sidx) (y : 'b):
   ! ISet.mem x (dom m) => (dom m.[x <- y]) = ISet.add x (dom m) by [].

lemma add_FSet(X : 'a set) (x : 'a):
  ISet.Finite.fromFSet (add x X) = ISet.add x (ISet.Finite.fromFSet X).
proof strict.
  apply ISet.set_ext; rewrite /ISet.(==); smt.
qed.

lemma add_FSet2(X : 'a ISet.set) (x : 'a):
  ISet.Finite.finite X =>
  ISet.Finite.toFSet (ISet.add x X) = add x (ISet.Finite.toFSet X).
proof strict.
  progress.
  apply set_ext. rewrite /FSet.(==).
  intros => z.
  case (z = x). smt.
  progress.
    smt.
  smt.
qed.

lemma fdom_set_add(m : (Sidx,'b) map) (x : Sidx) (y : 'b):
   ! ISet.mem x (dom m) => (fdom m.[x <- y]) = add x (fdom m).
proof strict.
  rewrite /fdom /fdom. rewrite -add_FSet2. smt.
  smt.
qed.

(*
(** List case analysis *)
lemma fset_case: forall (p: 'a set cpred), 
    p FSet.empty => 
    (forall x s, p (add x s)) =>
    (forall s, p s)
by [].

lemma fset_case_eq: forall (p: 'a set cpred) (s:'a set),
    (s = FSet.empty => p s) =>
    (forall x s', s = add x s' => p s) =>
    p s.
proof strict.
  intros=> p s.
  elim/fset_case s => //.
  intros=> x s' _ h.
  apply (h x s').
qed.
*)

lemma iset_less_exists(X Y : 'a ISet.set):
  ISet.(<) X Y => exists x, ISet.mem x Y /\ ! ISet.mem x X by [].


lemma mem_ToISet(X : 'a set) (x : 'a):
   mem x X = ISet.mem x (ISet.Finite.fromFSet X) by [].

lemma less_ToISet(X Y : 'a set):
  (X < Y) = (ISet.(<) (ISet.Finite.fromFSet X) (ISet.Finite.fromFSet Y)) by [].

lemma fset_less_exists(X Y : 'a set):
  X < Y => exists x, mem x Y /\ ! mem x X.
proof strict.
  rewrite less_ToISet. smt.
qed.

lemma mem_pick_filter(X Y : 'a set):
  X < Y => ! mem (pick (filter (lambda x, !mem x X) Y)) X.
proof strict.
  intros=> Hless. apply not_def => Hmem_pick.
  cut H: mem (pick (filter (lambda (x : 'a), ! mem x X) Y))
             (filter (lambda (x : 'a), ! mem x X) Y).
   apply mem_pick.
   apply not_def.
   cut L: exists x, mem x ( filter (lambda (x : 'a), ! mem x X) Y); last by smt.
   cut J:
       (exists (x : 'a), mem x (filter (lambda (x0 : 'a), ! mem x0 X) Y))
     = (exists (x : 'a), mem x Y /\ ! mem x X).
     cut R: forall x,   mem x (filter (lambda (x0 : 'a), ! mem x0 X) Y)
                      = (mem x Y /\ ! mem x X). smt.
     smt.
   rewrite J.
   progress.
   apply fset_less_exists => //.
   generalize H. rewrite mem_filter. progress. smt.
qed.

require import Sum.

local
lemma pr_AKE_3_2 &m:
    Pr[ AKE_3_2(A).main() @ &m: AKE_3_2.bad_esk_col ]
    <= qSession%r * qSession%r * (1%r /(card univ_Esk)%r).
proof strict.
  fel 2
      (card (fdom AKE_3_2.mEsk))
      (lambda x, qSession%r * (1%r /(card univ_Esk)%r))
      qSession
      AKE_3_2.bad_esk_col
      [AKE_3_2(A).sample : (fdom AKE_3_2.mEsk <> univ_Sidx) ].
        (* precond for increasing counter *)
  (* bound is right: sum .. = b *)
  cut G:= Sum.int_sum_const
           (lambda (x : int), qSession%r * (1%r / (card univ_Esk)%r))
           (intval 0 (qSession - 1)).
  rewrite (G _). smt.
  progress.
  rewrite intval_card_0. smt. smt.
  (* post implied *)
  progress; smt.
  (* init ensures !bad and counter 0 *)
  wp. skip.
    intros=> &hr _. split. trivial.
    by rewrite fdom_empty card_empty //.
  (* bound probability of setting bad in one execution of sample *)
  fun.
  if; first 1 last.
    conseq (_ : _ : =  0%r); first progress; apply zero_leq_divr; smt.
      by hoare; skip; smt.
  wp.
  sp.
  rnd (lambda x, bad_esk_col_x_op AKE_3_2.mEsk x).
  skip.
  progress.
  rewrite /sample_Esk Duni.mu_def; first by smt.
  apply leq_div; first by smt.
  apply leq_real_int.
  apply (int_leq_trans _ (card (frng AKE_3_2.mEsk{hr})) _); last by smt.
    by apply card_leq; smt.
  smt.
  (* sample increases counter if precond is satisfied *)
  progress. fun. rcondt 1. skip; smt.
  wp. rnd. wp. skip; progress.
  cut Hnotin:
      ! ISet.mem (pick (filter (lambda x, !mem x (fdom AKE_3_2.mEsk{hr})) univ_Sidx))
                 (dom AKE_3_2.mEsk{hr}).
    rewrite -mem_fdom.
    apply mem_pick_filter. smt.
  rewrite fdom_set_add // card_add_nin. rewrite mem_fdom //. smt.
  smt.
  (* if precond is not satisfied, counter is not increased *)
  progress.
  fun. wp. rcondf 1. skip; smt. skip; smt.
qed.

(*{ end: Proof: Bound probability of bad_esk_col *)

(* Split mH1 into mEexp and mH1A. *)
module AKE_4(FA : Adv) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH1, cH2 : int                  (* counters for queries *)

  var mH1A : ((Sk * Esk), Eexp) map   (* map for h1_a *)
  var sH1  : (Sk * Esk) set           (* adversary queries for h1 *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEsk       : (Sidx, Esk) map    (* map for ephemeral secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  var bad_esk_col : bool              (* esk collision *)
    (* There are two session indexes with the same ephemeral key. *)

  var bad_esk_norev : bool            (* h1_a query without previous reveal *)
    (* There is a h1_a(x,_) query such that Ex i. mEsk[i] = Some x and no EphemeralRev for i *)

  fun init() : unit = {
    evs = [];
    test = None;
    cH1 = 0;
    cH2 = 0;
    mH1 = Map.empty;
    sH1 = FSet.empty;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mSk = Map.empty;
    mEsk = Map.empty;
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_esk_col = false;
    bad_esk_norev = false;
  }

  module O : AKE_Oracles = {

    fun h1(a : Sk, x : Esk) : Eexp = {
      var e : Eexp;
      e = $sample_Eexp;
      if (!in_dom (a,x) mH1) {
        mH1.[(a,x)] = e;
      } 
      return proj mH1.[(a,x)];
    }

    fun h1_a(a : Sk, x : Esk) : Eexp option = {
      var r : Eexp option = None;
      var xe : Eexp;
      if (bad_esk_norev_op mEsk mStarted mEexp x evs)
        bad_esk_norev = true;
      (* modify here *)
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
      var pX : Epk;
      var x : Esk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        x = proj mEsk.[i];
        (* modify here *)
        mEexp.[i] = h1(proj (mSk.[A]),x);
        pX = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (A,B,init);
        r = Some(pX);
        evs = Start(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var y : Esk;
      var pY : Epk;
      var r : Epk option = None; 
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        y = proj mEsk.[i];
        (* modify here *)
        mEexp.[i] = h1(proj (mSk.[B]),y);
        pY = gen_epk(proj mEexp.[i]);
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        r = Some(pY);
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      if (!in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
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
      if (in_dom i mStarted && in_dom i mEexp) {
        r = mEsk.[i];
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
      }
      return r;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var sd : Sdata2;
      var k : Key;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        sd = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd));
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        evs = SessionRev(compute_sid mStarted mEexp mCompleted i)::evs;
        r = computeKey(i);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : bool = {
    var b : bool = def;
    var pks : Pk list = [];
    var t_idx : Sidx = def;
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx = def;
    var ska : Sk = def;
    var pka : Pk = def;

    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      mEsk.[sidx] = $sample_Esk;
    } 

    if (bad_esk_col_op mEsk) bad_esk_col = true;
    
    t_idx = A.choose(pks);
    b = ${0,1};
    if (in_dom t_idx mStarted && in_dom t_idx mCompleted && in_dom t_idx mEexp) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
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

lemma Pr_AKE_1_bad(A <: Adv) &m:
       Pr[ AKE_1(A).main() @ &m : res /\ test_fresh AKE_1.test AKE_1.evs ]
  <=   Pr[ AKE_1(A).main() @ &m : res /\ test_fresh AKE_1.test AKE_1.evs /\
                                  !AKE_1.bad_esk_norev /\ !AKE_1.bad_esk_col]
     + Pr[ AKE_1(A).main() @ &m : AKE_1.bad_esk_col ]
     + Pr[ AKE_1(A).main() @ &m : (! AKE_1.bad_esk_col) /\ AKE_1.bad_esk_norev ].
proof strict.
  admit.
qed.

(*} end: Proof: Pr[ AKE : win ] <= eps + Pr[ AKE_EexpRev : win ] *)
*)