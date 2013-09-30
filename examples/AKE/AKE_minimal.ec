require import Bool.
require import Int.
require import Map.
require import FSet.
require import List.
require import Fun.
require import Real.
require import Pair.

require import AKE_defs.

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
     ( ! (in_dom i mStarted) \/
       ! (mem (EphemeralRev (compute_psid mStarted mEexp i)) evs))).

(* Add bad flags bad_esk_col and bad_esk_guess *)
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
      if (cH1 < qH1) {
        cH1 = cH1 + 1;
        sH1 = add (a,x) sH1;
        if (bad_esk_norev_op mEsk mStarted mEexp x evs) {
          bad_esk_norev = true;
        }
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
    return (b = b');
  }
}.

lemma Eq_AKE_3_AKE_3__1_bad_esk_norev(A <: Adv):
  equiv[ AKE_3(A).main ~ AKE_3(A).main : true ==>
            AKE_3.bad_esk_norev{1} =>  AKE_3.bad_esk_norev{2} ].
proof strict.
  fun.
(*  conseq (_ : _ ==> ={AKE_3.bad_esk_norev}) => //.
   eqobs_in.  
save. *)
  inline AKE_3(A).init.
  (* 1: this takes about 5 seconds *)
(*  seq 11 11:
    ( ={b,pks,t_idx,key,keyo,b',i,sidx, sidxs,ska,pka}).
  eqobs_in true true:
    ( ={b,pks,t_idx,key,keyo,b',i,sidx, sidxs,ska,pka}). *)
  (* 2: this takes about 31 seconds *)

  seq 25 25:
    ( ={b,pks,t_idx,key,keyo,b',i,sidx, sidxs,ska,pka} /\
      AKE_3.evs{1}         = AKE_3.evs{2} /\
      AKE_3.test{1}        = AKE_3.test{2} /\
      AKE_3.cH1{1}         = AKE_3.cH1{2} /\
      AKE_3.cH2{1}         = AKE_3.cH2{2} /\
      AKE_3.mH1{1}         = AKE_3.mH1{2} /\
      AKE_3.sH1{1}         = AKE_3.sH1{2} /\
      AKE_3.mH2{1}         = AKE_3.mH2{2} /\
      AKE_3.sH2{1}         = AKE_3.sH2{2} /\
      AKE_3.mSk{1}         = AKE_3.mSk{2} /\
      AKE_3.mCompleted{1}  = AKE_3.mCompleted{2} /\
      AKE_3.mStarted{1}    = AKE_3.mStarted{2} /\
      AKE_3.mEsk{1}        = AKE_3.mEsk{2} /\
      AKE_3.mEexp{1}       = AKE_3.mEexp{2}).
  eqobs_in. 

  admit.
qed.


