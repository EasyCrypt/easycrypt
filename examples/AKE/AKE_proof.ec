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

  var cSession, cH1, cH2 : int        (* counters for queries *)

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
  let (A,B,r) = proj mStarted.[i] in
  (A,B,gen_epk(proj mEexp.[i]),proj mCompleted.[i],r).

op compute_psid(mStarted : (Sidx, Sdata2) map) (mEexp : (Sidx, Eexp) map)
               (i : Sidx) : Psid =
  let (A,B,r) = proj mStarted.[i] in (A,B,gen_epk(proj mEexp.[i]),r).

module AKE_EexpRev(FA : Adv2) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  
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
      if (cSession < qSession && in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        cSession = cSession + 1;
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
      if (   cSession < qSession && in_dom A mSk && in_dom B mSk
          && !in_dom i mStarted && !in_dom i mCompleted) {
        cSession = cSession + 1;
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
      if (in_dom i mCompleted) {
        (a,b,ro) = proj mStarted.[i];
        k = h2(gen_sstring (proj mEexp.[i]) (proj mSk.[a]) b (proj mCompleted.[i]) ro);
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted) {
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
    var xa' : Eexp = def;
    
    mSk = Map.empty;
    while (i < qAgent) {
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
    }
    
    mEexp = Map.empty;
    i = 0;
    while (i < qSession) {
      xa' = $sample_Eexp;
      mEexp.[i] = xa';
    } 

    cSession = 0;
    cH1 = 0;
    cH2 = 0;
    mH2 = Map.empty;
    sH2 = FSet.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    evs = [];
    test = None;

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

pred collision_eexp_eexp(m : (int, Eexp) map) =
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

op esk_of_sidx (mStarted : (Sidx, Sdata) map) (i : Sidx) =
  sd_esk(proj mStarted.[i]).

op esks(mStarted : (Sidx, Sdata) map) : Esk set =
  img sd_esk (frng mStarted).

print op fdom.

op queried_esks(mH1 : ((Sk * Esk), Eexp)  map) : Esk set =
  img snd (fdom mH1).

(* Introduce bad flags for collision events *)
module AKE_1(FA : Adv) = {
  
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

  var bad_esk_col : bool              (* esk collision with dom(mH1) *)
    (* The esk sampled in init1/resp is already in dom(mH1). Since
       dom(mH1) = sH1 u <earlier esks>, this corresponds to
       esk-earlier-esk collisions and esk-earlier-h1_a collisions *)

  var bad_esk_norev : bool            (* h1_a query without previous reveal *)
  

  fun init() : unit = {
    evs = [];
    test = None;
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
      if (cH1 < qH1) {
        cH1 = cH1 + 1;
        if (any (lambda i, let sd = proj mStarted.[i] in
                           sd_esk sd = x /\
                           ! (mem (EphemeralRev (psid_of_sdata sd)) evs))
                (fdom mStarted)) {
          bad_esk_norev = true;
        }
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
        if (mem x (queried_esks mH1)) bad_esk_col = true;
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
        if (mem y (queried_esks mH1)) bad_esk_col = true;
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

lemma Eq_AKE_AKE_1_O_h1(A <: Adv{AKE, AKE_1}):
  equiv[ AKE(A).O.h1 ~ AKE_1(A).O.h1 :
         (AKE.mH1{1} = AKE_1.mH1{2} /\ AKE.sH1{1} = AKE_1.sH1{2} /\ ={x,a})
         ==> (AKE.mH1{1} = AKE_1.mH1{2} /\ AKE.sH1{1} = AKE_1.sH1{2} /\ ={res}) ].
  fun.
  eqobs_in.
qed.


lemma Eq_AKE_AKE_1(A <: Adv{AKE, AKE_1}):
  equiv[ AKE(A).main ~ AKE_1(A).main : true ==>
            (res /\ test_fresh AKE.test AKE.evs){1}
         => (res /\ test_fresh AKE_1.test AKE_1.evs){2}].
proof strict.
  fun.
  eqobs_in
    (AKE.mSk{1}        = AKE_1.mSk{2} /\
     AKE.cSession{1}   = AKE_1.cSession{2} /\
     AKE.cH1{1}        = AKE_1.cH1{2} /\
     AKE.cH2{1}        = AKE_1.cH2{2} /\
     AKE.mH1{1}        = AKE_1.mH1{2} /\
     AKE.sH1{1}        = AKE_1.sH1{2} /\
     AKE.mH2{1}        = AKE_1.mH2{2} /\
     AKE.sH2{1}        = AKE_1.sH2{2} /\
     AKE.mStarted{1}   = AKE_1.mStarted{2} /\
     AKE.mCompleted{1} = AKE_1.mCompleted{2} /\
     AKE.evs{1}        = AKE_1.evs{2} /\
     AKE.test{1}       = AKE_1.test{2})
    true :
    (={b,pks,t_idx,key,keyo,b',i,ska,pka} /\
     AKE.mSk{1}        = AKE_1.mSk{2} /\
     AKE.cSession{1}   = AKE_1.cSession{2} /\
     AKE.cH1{1}        = AKE_1.cH1{2} /\
     AKE.cH2{1}        = AKE_1.cH2{2} /\
     AKE.mH1{1}        = AKE_1.mH1{2} /\
     AKE.sH1{1}        = AKE_1.sH1{2} /\
     AKE.mH2{1}        = AKE_1.mH2{2} /\
     AKE.sH2{1}        = AKE_1.sH2{2} /\
     AKE.mStarted{1}   = AKE_1.mStarted{2} /\
     AKE.mCompleted{1} = AKE_1.mCompleted{2} /\
     AKE.evs{1}        = AKE_1.evs{2} /\
     AKE.test{1}       = AKE_1.test{2}).
    (* resp *)
    fun.
    sp.
    if; [ smt | | skip; smt].
    sp. wp.
    call (Eq_AKE_AKE_1_O_h1 A).
    wp.
    rnd. skip. smt.
    (* init1 *)
    fun.
    sp.
    if; [ smt | | skip; smt].
    sp. wp.
    call (Eq_AKE_AKE_1_O_h1 A).
    wp.
    rnd. skip. smt.
    (* h1_a *)
    fun.
    sp.
    if; [ smt | | skip; smt].
    sp. wp.
    call (Eq_AKE_AKE_1_O_h1 A).
    skip. smt.
qed.

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