require import Option.
require import List.
require import Map.
require import FSet.
require import Int.
require import AKE_defs.
require import Real.

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

op get_string_from_id (i : Sidx)(mStarted : (Sidx, Sdata2) map)(mCompleted : (Sidx, Epk)   map) mEexp mSk : Sstring =
let (a,b,ro) = proj mStarted.[i] in
gen_sstring (proj mEexp.[i]) (proj mSk.[a]) b (proj mCompleted.[i]) ro.

op fresh_op : Sid -> Event list-> bool.

axiom fresh_op_def : forall s evs,
fresh s evs <=> fresh_op s evs = true.

lemma fresh_op_def' : forall s evs,
fresh s evs = (fresh_op s evs = true) by smt.





module type AKE_Oracles3 = {
  fun eexpRev(i : Sidx, a : Sk) : Eexp option
  fun init1(i : Sidx, A : Agent, B : Agent) : Epk option
  fun init2(i : Sidx, Y : Epk) : unit
  fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option
  fun staticRev(A : Agent) : Sk option
  fun eqS(i : Sidx, ss: Sstring) : bool option
}.

module type Adv3 (O : AKE_Oracles3) = {
  fun guess(s : Pk list) : (Sstring list * Sidx) {* O.eexpRev O.init1 O.init2 O.resp O.staticRev O.eqS}
}.

pred collision_eexp_eexp(m : (Sidx, Eexp) map) =
  exists i j, in_dom i m /\ m.[i] = m.[j] /\ i <> j.

pred collision_eexp_rcvd(evs : Event list) =
  exists (i : int) (j : int) s1 s2 s3,
     0 <= i /\ 0 <= j /\ i < length evs /\
     i > j /\  nth evs i = Some (Accept s1) /\
     (   (nth evs j  = Some (Start s2)  /\ psid_sent s2 = sid_rcvd s1)
      \/ (nth evs j  = Some (Accept s3) /\ sid_sent s3 = sid_rcvd s1 /\ sid_role s3 = resp)).

op collision_eexp_rcvd_op : Event list -> bool.

axiom collision_eexp_rcvd_op_def :
forall evs, 
(collision_eexp_rcvd_op evs) = 
(collision_eexp_rcvd evs). 

op collision_eexp_eexp_op : (Sidx, Eexp) map -> bool.

axiom collision_eexp_eexp_op_def :
forall eexps, 
(collision_eexp_eexp_op eexps) = 
(collision_eexp_eexp eexps). 


module AKE_eqS(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  var h2_queries : Sstring list
  var test_sidx  : Sidx
    
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles3 = {
    
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

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
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
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
  }
}.

op inv_gen_epk : Epk -> Eexp.

axiom inv_gen_epk_def : forall x, x = inv_gen_epk (gen_epk x).

lemma gen_epk_inj : forall e1 e2,
gen_epk e1 = gen_epk e2 =>
e1 = e2.
proof.
 intros => e1 e2 heq.
 by rewrite (inv_gen_epk_def e1) (inv_gen_epk_def e2) heq.
save.

module type AKE_Leaf1_Oracle = {
  fun eqS(A : Pk, b : Sk, X Y : Epk, r : Role, ss: Sstring) : bool option
}.

module type Adv_Leaf1 (O : AKE_Leaf1_Oracle) = {
 fun guess(A : Pk, lepk : Epk list ) : Sk  {* O.eqS}
}.



module Leaf1 (A :  Adv_Leaf1) = {
 var sk : Sk
 var lepk : Epk list
 module O : AKE_Leaf1_Oracle = {

  fun eqS(A : Pk, b : Sk, X Y : Epk, r : Role, ss: Sstring) : bool option = {
   var ret : bool option = None;
   if (gen_pk sk = A /\ mem X lepk)
    ret = Some (ss = gen_sstring (inv_gen_epk X) sk (gen_pk b) Y r);
   return ret;
  }
 }
 module Adv = A(O)
 fun main() : bool = {
  var sk' : Sk;
  var sidxs : Sidx set = univ_Sidx;
  var sidx : Sidx;
  var xa' : Eexp;
  sk = $sample_Sk;
  lepk = [];
  while (sidxs <> FSet.empty) {
   sidx = pick sidxs;
   sidxs = rm sidx sidxs;
   xa' = $sample_Eexp;
   lepk = (gen_epk xa') :: lepk;
  }
  sk' = Adv.guess(gen_pk (sk) , lepk);
  return (sk = sk');
 }
}.

section.

declare module A : Adv3{ AKE_eqS, Leaf1}.

axiom A_ll :
forall (O <: AKE_Oracles3{A}),
  islossless O.eexpRev =>
  islossless O.init1 =>
  islossless O.init2 =>
  islossless O.resp =>
  islossless O.staticRev => islossless O.eqS => islossless A(O).guess.

local module G1(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)

  var h2_queries : Sstring list
  var test_sidx  : Sidx
  var bad : bool
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
  }

  module O : AKE_Oracles3 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted /\ !bad) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
   if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
      if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
          r = mEexp.[i];
        } else bad = true;
   
      }
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
      if (in_dom A mSk /\ ! bad) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
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
    bad = false;
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
  }
}.

local equiv Eq1 : AKE_eqS(A).main ~ G1(A).main : true ==> 
(AKE_eqS.h2_queries{1} = G1.h2_queries{2} /\
 AKE_eqS.test_sidx{1} = G1.test_sidx{2} /\ 
 AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2}) \/ G1.bad{2}.
proof.
 fun.
 seq 16 17:
(AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.test{1} = G1.test{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2} /\
 AKE_eqS.h2_queries{1} = G1.h2_queries{2} /\
 AKE_eqS.test_sidx{1} = G1.test_sidx{2} /\
 ={pks} /\ 
 ! G1.bad{2}).
wp.
simplify.
eqobs_in.
if => //.
call (_ : G1.bad, 
 AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.test{1} = G1.test{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2}).
 by apply A_ll.
 by fun; wp; skip; progress; smt.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial.
 by intros => ?; fun; wp; skip; progress.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress.
 fun.
 wp; skip; progress; smt.

 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress.
 fun.
 wp; trivial; skip; progress; smt.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress.
 skip; progress => //; smt.
save.

op guess_session(test_sidx : Sidx,
                  mCompleted : (Sidx, Epk) map,
                  mStarted   : (Sidx, Sdata2) map, 
                  mEexp : (Sidx, Eexp) map, 
                  mSk : (Pk, Sk) map,
                  h2_queries : Sstring list,
                  evs : Event list) =
in_dom test_sidx mCompleted /\
List.mem
(get_string_from_id test_sidx mStarted 
  mCompleted mEexp mSk) 
(h2_queries) /\
fresh_op (compute_sid mStarted mEexp mCompleted test_sidx) evs.

local lemma Pr1 &m :
Pr[AKE_eqS(A).main() @ &m : guess_session AKE_eqS.test_sidx AKE_eqS.mCompleted 
                              AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mSk 
                              AKE_eqS.h2_queries AKE_eqS.evs] <=
Pr[G1(A).main() @ &m : guess_session G1.test_sidx G1.mCompleted G1.mStarted 
                                     G1.mEexp G1.mSk G1.h2_queries G1.evs] +
Pr[G1(A).main() @ &m : G1.bad].
proof.
apply (Real.Trans _ 
Pr[G1(A).main() @ &m :
   guess_session G1.test_sidx G1.mCompleted G1.mStarted G1.mEexp G1.mSk
     G1.h2_queries G1.evs \/ G1.bad]
 _ ).
equiv_deno Eq1 => //; smt.
rewrite Pr mu_or.
cut h: forall (a b c : real), 0%r <= c => a + b - c <= a + b by smt.
apply h; smt.
save.

local module G2(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mPkPos     : (Agent, int) map
  var h2_queries : Sstring list
  var test_sidx  : Sidx
  var bad : bool
  var bad_pk : Agent option
  var pk_guess : int
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_pk = None;
  }

  module O : AKE_Oracles3 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted /\ !bad) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
   if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
      if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
          r = mEexp.[i];
        } else
        {
         bad = true;
         bad_pk = Some (gen_pk a);
        }
      }
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
      if (in_dom A mSk /\ ! bad) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
    mPkPos = Map.empty;
    init();
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      xa' = $sample_Eexp;
      mEexp.[sidx] = xa';
    } 
    bad = false;
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
    pk_guess = $[1..qAgent];
  }
}.
pred is_sub_map (m1 : ('a, 'b) map)(m2 : ('a, 'c) map) =
forall x, in_dom x m1 => in_dom x m2.

lemma is_sub_map_upd1 : forall (m1 : ('a, 'b) map)(m2 : ('a, 'c) map) x v,
is_sub_map m1 m2 =>
is_sub_map m1 m2.[x<-v].
proof strict.
 intros => m1 m2 x v h s hdom.
 by rewrite in_dom_set; left; apply h.
save.


lemma is_sub_map_upd2 : forall (m1 : ('a, 'b) map)(m2 : ('a, 'c) map) x v1 v2,
is_sub_map m1 m2 =>
is_sub_map m1.[x<-v1] m2.[x<-v2].
proof strict.
 intros => m1 m2 x v1 v2 h s.
 rewrite in_dom_set => [|] h'.
  by rewrite in_dom_set; left; apply h.
  by rewrite h' in_dom_setE.
save.

lemma is_sub_map_upd3 : forall (m1 : ('a, 'b) map)(m2 : ('a, 'c) map) x v,
in_dom x m2 =>
is_sub_map m1 m2 =>
is_sub_map m1.[x<-v] m2.
proof strict.
 intros => m1 m2 x v1 h h' s.
 rewrite in_dom_set => [|] h''.
  by apply h'.
  by rewrite h''.
save.



local equiv Eq2 : G1(A).main ~ G2(A).main : true ==> 
G1.bad{1} => G2.bad{2} /\ (0 < (proj G2.mPkPos.[(proj G2.bad_pk)]) <= qAgent){2}.
proof.
 fun.
 seq 17 18: 
(={pks} /\
 G1.evs{1} = G2.evs{2} /\
 G1.test{1} = G2.test{2} /\
 G1.mSk{1} = G2.mSk{2} /\
 G1.mEexp{1} = G2.mEexp{2} /\
 G1.mStarted{1} = G2.mStarted{2} /\ 
 G1.mCompleted{1} = G2.mCompleted{2} /\
 G1.h2_queries{1} = G2.h2_queries{2} /\
 G1.test_sidx{1} = G2.test_sidx{2} /\
 (forall x, in_dom x G2.mSk => 0 < (proj G2.mPkPos.[x]) <= qAgent){2} /\
 G1.bad{1} = G2.bad{2} /\ ! G2.bad{2} /\
 G1.mStarted{1} = Map.empty /\
 G1.mCompleted{1} = Map.empty).
  wp; simplify.
 while (={sidxs} /\ G1.mEexp{1} = G2.mEexp{2}).
 wp; rnd; wp; skip; progress.
 while (G1.mSk{1} = G2.mSk{2} /\ ={i, pks} /\ 0 <= i{2} <= qAgent /\
(forall x, in_dom x G2.mSk => 0 < (proj G2.mPkPos.[x]) <= qAgent){2}).
wp; rnd; wp; skip; progress.
 smt.
 smt.
 case (x = gen_pk skaL).
  intros => ->; rewrite get_setE proj_some; smt.

  intros => h; generalize H7; rewrite in_dom_setNE ?get_setNE; first 2 smt.
   intros => h'; cut := H1 x _; smt.

 case (x = gen_pk skaL).
  intros => ->; rewrite get_setE proj_some; smt.
  intros => h; generalize H7; rewrite in_dom_setNE ?get_setNE; first 2 smt.
   intros => h'; cut := H1 x _; smt.

inline G1(A).init G2(A).init.
wp; skip; progress => //.
smt.
smt.
smt.
if => //.
rnd{2}.
call (_ :
 G1.evs{1} = G2.evs{2} /\
 G1.test{1} = G2.test{2} /\
 G1.mSk{1} = G2.mSk{2} /\
 G1.mEexp{1} = G2.mEexp{2} /\
 G1.mStarted{1} = G2.mStarted{2} /\ 
 G1.mCompleted{1} = G2.mCompleted{2} /\
 G1.bad{1} = G2.bad{2} /\ 
 (G2.bad{2} => 
  G2.bad_pk{2} <> None /\ in_dom (proj G2.bad_pk{2}) G2.mSk{2}) /\
 is_sub_map G2.mCompleted{2} G2.mStarted{2} /\
 (forall i, in_dom i G2.mStarted{2} => 
 in_dom (sd2_actor(proj G2.mStarted.[i])){2} G2.mSk{2} )).
fun; wp; skip; progress => //; first smt.
 by rewrite proj_some -H4; apply H1.
fun; wp; skip; progress => //.
by apply is_sub_map_upd1.
case (i{2} = i0).
 by intros => ->; rewrite get_setE proj_some /sd2_actor.
 intros => _; rewrite get_setNE //; apply H1; generalize H5;
  rewrite in_dom_setNE; smt.

by fun; wp; skip; progress => //; apply is_sub_map_upd3.
fun; wp; skip; progress => //.
 apply is_sub_map_upd2 => //.
case (i{2} = i0).
 by intros => ->; rewrite get_setE proj_some /sd2_actor.
 intros => _; rewrite get_setNE //; apply H1; generalize H6;
  rewrite in_dom_setNE; smt.
by fun; wp; skip; progress => //.
by fun; wp; skip; progress => //.
skip; progress => //.
smt.
smt.
rewrite /is_sub_map; smt.
smt.
rewrite -FSet.Dinter_uni.dinter_is_dinter FSet.Dinter_uni.weight_def; smt.
cut := H5 _ => //.
intros => [_ _].
cut := H (proj bad_pk_R) _ => //.
cut := H5 _ => //.
intros => [_ _].
cut := H (proj bad_pk_R) _ => //.
rnd{2};skip; progress.
rewrite -FSet.Dinter_uni.dinter_is_dinter FSet.Dinter_uni.weight_def; smt.
smt.
smt.
save.

local lemma Pr2 : forall &m,
Pr[G1(A).main() @ &m : G1.bad] <=
Pr[G2(A).main() @ &m : G2.bad /\ 
              0 < (proj G2.mPkPos.[(proj G2.bad_pk)]) <= qAgent].
proof.
 by intros => &m; equiv_deno Eq2.
save.

local lemma Pr3 : forall &m,
Pr[G1(A).main() @ &m : G1.bad] <=
qAgent%r * Pr[G2(A).main() @ &m : G2.bad /\ 
              (proj G2.mPkPos.[(proj G2.bad_pk)]) = G2.pk_guess].
proof.
 admit.
save.


local module G3(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mPkPos     : (Agent, int) map
  var h2_queries : Sstring list
  var test_sidx  : Sidx
  var bad : bool
  var bad_pk : Agent option
  var pk_guess : int
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_pk = None;
  }

  module O : AKE_Oracles3 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted /\ !bad) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
   if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
      if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
          r = mEexp.[i];
        } else
        {
         bad = true;
         bad_pk = Some (gen_pk a);
        }
      }
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
      if (in_dom A mSk /\ ! bad) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
    mPkPos = Map.empty;
    init();
    pk_guess = $[1..qAgent];
    while (i < pk_guess - 1) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    }
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    }

    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      xa' = $sample_Eexp;
      mEexp.[sidx] = xa';
    } 
    bad = false;
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
  }
}.


local equiv Eq3 : G2(A).main ~ G3(A).main : true ==> 
(G2.bad /\ (proj G2.mPkPos.[(proj G2.bad_pk)]) = G2.pk_guess){1} <=>
(G3.bad /\ (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess){2}.
proof.
 fun.
 swap{1} 20 -4.
 seq 17 24:
( ={sidxs, i} /\
  ={pks} /\
  G2.pk_guess{1} = G3.pk_guess{2} /\
  G2.mPkPos{1} = G3.mPkPos{2} /\
  G2.bad_pk{1} = G3.bad_pk{2} /\
  G2.mCompleted{1} = G3.mCompleted{2} /\
  G2.mStarted{1} = G3.mStarted{2} /\
  G2.mEexp{1} = G3.mEexp{2} /\ 
  G2.mSk{1} = G3.mSk{2} /\ G2.evs{1} = G3.evs{2});
  last by eqobs_in.
   
  inline G2(A).init G3(A).init; sp.
  splitwhile (i < G2.pk_guess - 1) : {1} 2.
  splitwhile (i = G2.pk_guess - 1) : {1} 3.
  eqobs_in.
  rcondt{1} 3.
  intros &m; wp.
  while (i <= G2.pk_guess - 1 /\ G2.pk_guess <= qAgent).
  wp; rnd; wp; skip; smt.
  rnd; wp; skip; progress; last 3 by smt.
   cut: 1 <= pk_guess; smt.
  rcondf{1} 9.
  intros &m; wp; rnd; wp.
  while (i <= G2.pk_guess - 1 /\ G2.pk_guess <= qAgent).
  wp; rnd; wp; skip; smt.
  rnd; wp; skip; progress; last 2 smt.
  cut: 1 <= pk_guess; smt.
  wp; rnd; wp.     
  while (={i, ska, pka, pks} /\ G2.mSk{1} = G3.mSk{2} /\ 
   G2.mPkPos{1} = G3.mPkPos{2} /\ G2.mPkPos{1} = G3.mPkPos{2} /\
   G2.pk_guess{1} = G3.pk_guess{2} /\
   G2.pk_guess{1} <= qAgent ).
  wp; rnd; wp; skip; progress; smt.
  rnd; skip; progress.
  smt.
save.

local lemma Pr4 &m :
Pr[G2(A).main() @ &m : G2.bad /\ 
              (proj G2.mPkPos.[(proj G2.bad_pk)]) = G2.pk_guess] =
Pr[G3(A).main() @ &m : G3.bad /\ 
              (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess].
proof.
 by equiv_deno Eq3.
save.


local lemma Pr5 &m :
Pr[AKE_eqS(A).main() @ &m : 
 guess_session AKE_eqS.test_sidx AKE_eqS.mCompleted 
               AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mSk 
               AKE_eqS.h2_queries AKE_eqS.evs] <=
Pr[G1(A).main() @ &m : guess_session G1.test_sidx G1.mCompleted G1.mStarted 
                                     G1.mEexp G1.mSk G1.h2_queries G1.evs] +
qAgent%r * 
Pr[G3(A).main() @ &m : G3.bad /\ 
              (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess].
proof.
 rewrite -(Pr4 &m).
 apply (Real.Trans _ (Pr[G1(A).main() @ &m :
   guess_session G1.test_sidx G1.mCompleted G1.mStarted G1.mEexp G1.mSk
     G1.h2_queries G1.evs] +
       Pr[G1(A).main() @ &m : G1.bad] ) _ ).
apply (Pr1 &m).
apply (_ : forall (a b c : real),  b <= c => a + b <= a + c); first smt.
by apply (Pr3 &m).
save.

(* we move the sampling from main to init1 and resp: 
this step is justified by some kind of eager sampling *)
 
local module G4(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mPkPos     : (Agent, int) map
  var h2_queries : Sstring list
  var test_sidx  : Sidx
  var bad : bool
  var bad_pk : Agent option
  var pk_guess : int
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_pk = None;
  }

  module O : AKE_Oracles3 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted /\ !bad) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
   if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
      if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
          r = mEexp.[i];
        } else
        {
         bad = true;
         bad_pk = Some (gen_pk a);
        }
      }
     }
      return r;
    }

    fun init1(i : Sidx, A : Agent, B : Agent) : Epk option = {
      var pX : Epk;
      var r : Epk option = None; 
      var xa' : Eexp;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        if (!in_dom i mEexp) {
          xa' = $sample_Eexp;
          mEexp.[i] = xa';
        }
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
      var xa' : Eexp;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        if (!in_dom i mEexp) {
         xa' = $sample_Eexp;
         mEexp.[i] = xa';
       }
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
      if (in_dom A mSk /\ ! bad) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
    mPkPos = Map.empty;
    init();
    pk_guess = $[1..qAgent];
    ska = $sample_Sk;
    pka = gen_pk(ska);
    pks = pka :: pks;
    mSk.[pka] = ska;
    mPkPos.[pka] = pk_guess;
    while (i < pk_guess - 1) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    }
     i = i + 1;
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    } 
    bad = false;
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
  }
}.

local equiv Eq4 : G3(A).main ~ G4(A).main : true ==> 
(G3.bad /\ (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess){1} <=>
(G4.bad /\ (proj G4.mPkPos.[(proj G4.bad_pk)]) = G4.pk_guess){2}.
proof.
 admit.
save.

local lemma Pr6 &m :
Pr[G3(A).main() @ &m : G3.bad /\ 
              (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess] =
Pr[G4(A).main() @ &m : G4.bad /\ 
              (proj G4.mPkPos.[(proj G4.bad_pk)]) = G4.pk_guess].
proof.
 equiv_deno Eq4 => //.
save.

pred bad_eph_query (evs : Event list) A  =
exists j, exists B, exists X, exists r, 
0 <= j /\
nth evs j = Some (EphemeralRev(A,B,X,r)) /\
(forall k, j < k < length evs => nth evs k <> Some (StaticRev A)).

lemma bad_eph_query_mon : 
forall evs e A,
bad_eph_query evs A => 
bad_eph_query (e:: evs) A.
proof.
 intros => evs e A [j] B X r [hle] [h] hnot.
 exists (j+1); exists B; exists X; exists r.
 rewrite !nth_consN; first smt.
 rewrite (_ : j + 1 - 1 = j) ?h /=; first smt.
 split; first smt.
  progress => //.
  rewrite nth_consN; first smt.
  by apply hnot; generalize H0; rewrite length_cons; smt.
save.


local equiv Eq5 : G4(A).main ~ G4(A).main : true ==> 
(G4.bad /\ (proj G4.mPkPos.[(proj G4.bad_pk)]) = G4.pk_guess){1} =>
(bad_eph_query G4.evs (proj G4.bad_pk)){2}.
proof.
 fun; sp.
 seq 11 11:
(G4.evs{1} = G4.evs{2} /\
 G4.test{1} = G4.test{2} /\
 G4.mSk{1} = G4.mSk{2} /\
 G4.mEexp{1} = G4.mEexp{2} /\
 G4.mStarted{1} = G4.mStarted{2} /\ 
 G4.mCompleted{1} = G4.mCompleted{2} /\
 G4.h2_queries{1} = G4.h2_queries{2} /\
 G4.test_sidx{1} = G4.test_sidx{2} /\
 G4.bad{1} = G4.bad{2} /\
 ={pks} /\ 
 ! G4.bad{2}).
 wp;  while (={i, ska, pka, pks} /\ G4.mSk{1} = G4.mSk{2} /\ 
   G4.mPkPos{1} = G4.mPkPos{2} /\ G4.mPkPos{1} = G4.mPkPos{2} /\
   G4.pk_guess{1} = G4.pk_guess{2} /\
   G4.pk_guess{1} <= qAgent ). 
  wp; rnd; wp => //; skip; progress.
 wp;  while (={i, ska, pka, pks} /\ G4.mSk{1} = G4.mSk{2} /\ 
   G4.mPkPos{1} = G4.mPkPos{2} /\ G4.mPkPos{1} = G4.mPkPos{2} /\
   G4.pk_guess{1} = G4.pk_guess{2} /\
   G4.pk_guess{1} <= qAgent ).
  wp; rnd; wp => //; skip; progress.
  inline G4(A).init; wp; do 2! rnd; wp; skip; progress; smt.
  if => //; last by skip; progress; smt.
  call (_ : 
  (G4.bad{1} /\ proj G4.mPkPos{1}.[proj G4.bad_pk{1}] = G4.pk_guess{1} =>
  bad_eph_query G4.evs{2} (proj G4.bad_pk{2})) /\
  G4.evs{1} = G4.evs{2} /\
  G4.test{1} = G4.test{2} /\
  G4.mSk{1} = G4.mSk{2} /\
  G4.mEexp{1} = G4.mEexp{2} /\
  G4.mStarted{1} = G4.mStarted{2} /\ 
  G4.mCompleted{1} = G4.mCompleted{2} /\
  G4.h2_queries{1} = G4.h2_queries{2} /\
  G4.test_sidx{1} = G4.test_sidx{2} /\
  G4.bad{1} = G4.bad{2}).
  fun.
  wp; skip; progress; try smt.
  rewrite proj_some.
  generalize H2 H3; rewrite  /compute_psid /psid_actor /sd2_actor.
  elim /tuple3_ind ( proj (G4.mStarted{2}.[i{2}])) => A B r /= heq heq' hmem.
  rewrite /bad_eph_query.
  exists 0; exists B; exists (gen_epk (proj G4.mEexp{2}.[i{2}])); 
  exists r; progress.
  by rewrite nth_cons0 heq'.
  rewrite not_def.
  intros => h; generalize hmem => /=.
  rewrite -(proj_some ((StaticRev A))) heq' -h heq'.
  by apply nth_mem;  smt.
  by trivial.  
  fun; sp; if => //; if => //; wp; try rnd; skip; progress.
  apply bad_eph_query_mon; apply H => //.
  apply bad_eph_query_mon; apply H => //.

  fun; wp; skip; progress => //.
  apply bad_eph_query_mon; apply H => //.

  fun; sp; if => //; if => //; wp; try rnd; skip; progress.
  apply bad_eph_query_mon; apply H => //.
  apply bad_eph_query_mon; apply H => //.

  fun; wp; skip; progress => //.
  apply bad_eph_query_mon; apply H => //.

  fun; wp; skip; progress => //.
  apply bad_eph_query_mon; apply H => //.
  skip; progress => //; smt.
save.

local lemma Pr7 &m :
Pr[G4(A).main() @ &m : G4.bad /\ 
              (proj G4.mPkPos.[(proj G4.bad_pk)]) = G4.pk_guess] <=
Pr[G4(A).main() @ &m :bad_eph_query G4.evs (proj G4.bad_pk)].
proof.
 equiv_deno Eq5 => //.
save.


local lemma Pr8 &m :
Pr[AKE_eqS(A).main() @ &m : 
 guess_session AKE_eqS.test_sidx AKE_eqS.mCompleted 
               AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mSk 
               AKE_eqS.h2_queries AKE_eqS.evs] <=
Pr[G1(A).main() @ &m : guess_session G1.test_sidx G1.mCompleted G1.mStarted 
                                     G1.mEexp G1.mSk G1.h2_queries G1.evs] +
qAgent%r * 
Pr[G4(A).main() @ &m :bad_eph_query G4.evs (proj G4.bad_pk)].
proof.
apply (Real.Trans _ (Pr[G1(A).main() @ &m : guess_session G1.test_sidx G1.mCompleted G1.mStarted 
                                     G1.mEexp G1.mSk G1.h2_queries G1.evs] +
qAgent%r * 
Pr[G3(A).main() @ &m : G3.bad /\ 
              (proj G3.mPkPos.[(proj G3.bad_pk)]) = G3.pk_guess]
) _ ).
apply (Pr5 &m).
rewrite (Pr6 &m).
apply (_ : forall (p q r : real), q <= r => p + q <= p + r); first smt.
cut  _ := Pr7 &m.
apply (_ : forall (p q : real) (i : int), p <= q => 0 <= i => i%r * p <= i%r * q) => //; first admit.
smt.
save.


local module G5(FA : Adv3) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mPkPos     : (Agent, int) map
  var h2_queries : Sstring list
  var test_sidx  : Sidx
  var bad : bool
  var bad_pk : Agent option
  var pk_guess : int
  var pk_guess_val : Agent
  fun init() : unit = {
    evs = [];
    test = None;
    mSk = Map.empty;    
    mEexp = Map.empty;
    mStarted = Map.empty;
    mCompleted = Map.empty;
    bad_pk = None;
  }

  module O : AKE_Oracles3 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted /\ !bad) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
   if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
      if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
          r = mEexp.[i];
        } else
        {
         bad = true;
         bad_pk = Some (gen_pk a);
        }
      }
     }
      return r;
    }

    fun init1(i : Sidx, A : Agent, B : Agent) : Epk option = {
      var pX : Epk;
      var r : Epk option = None; 
      var xa' : Eexp;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted) {
        if (!in_dom i mEexp) {
          xa' = $sample_Eexp;
          mEexp.[i] = xa';
        }
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
      var xa' : Eexp;
      if (in_dom A mSk && in_dom B mSk && !in_dom i mStarted && !in_dom i mCompleted) {
        if (!in_dom i mEexp) {
         xa' = $sample_Eexp;
         mEexp.[i] = xa';
       }
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
      if (in_dom A mSk /\ ! bad /\ (proj mPkPos.[A]) <> pk_guess) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        ev = SessionRev(compute_sid mStarted mEexp mCompleted i);
        if (! mem ev evs) { evs = ev::evs; }
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
  }
  
  module A = FA(O)

  fun main() : unit = {
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
    test_sidx = def;
    h2_queries = def;
    mPkPos = Map.empty;
    init();
    pk_guess = $[1..qAgent];
    ska = $sample_Sk;
    pka = gen_pk(ska);
    pks = pka :: pks;
    mSk.[pka] = ska;
    mPkPos.[pka] = pk_guess;
    pk_guess_val = pka;
    while (i < pk_guess - 1) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    }
     i = i + 1;
    while (i < qAgent) {
      i = i + 1;
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      mPkPos.[pka] = i;
    } 
    bad = false;
    if (!collision_eexp_eexp_op mEexp) {
     (h2_queries, test_sidx) = A.guess(pks);
    }
  }
}.

local equiv Eq5 : G4(A).main ~ G5(A).main : true ==> 
(G4.bad /\ (proj G4.mPkPos.[(proj G4.bad_pk)]) = G4.pk_guess){1} =>
(bad_eph_query G4.evs (proj G4.bad_pk)){2}.
proof.
 fun; sp.
 seq 11 12:
(G4.evs{1} = G5.evs{2} /\
 G4.test{1} = G5.test{2} /\
 G4.mSk{1} = G5.mSk{2} /\
 G4.mEexp{1} = G5.mEexp{2} /\
 G4.mStarted{1} = G5.mStarted{2} /\ 
 G4.mCompleted{1} = G5.mCompleted{2} /\
 G4.h2_queries{1} = G5.h2_queries{2} /\
 G4.test_sidx{1} = G5.test_sidx{2} /\
 G4.bad{1} = G5.bad{2} /\
 ={pks} /\ 
 ! G5.bad{2}).
 wp;  while (={i, ska, pka, pks} /\ G4.mSk{1} = G5.mSk{2} /\ 
   G4.mPkPos{1} = G5.mPkPos{2} /\ G4.mPkPos{1} = G5.mPkPos{2} /\
   G4.pk_guess{1} = G5.pk_guess{2} /\
   G4.pk_guess{1} <= qAgent ). 
  wp; rnd; wp => //; skip; progress.
 wp;  while (={i, ska, pka, pks} /\ G4.mSk{1} = G5.mSk{2} /\ 
   G4.mPkPos{1} = G5.mPkPos{2} /\ G4.mPkPos{1} = G5.mPkPos{2} /\
   G4.pk_guess{1} = G5.pk_guess{2} /\
   G4.pk_guess{1} <= qAgent ).
  wp; rnd; wp => //; skip; progress.
  inline G4(A).init G5(A).init; wp; do 2! rnd; wp; skip; progress; smt.
  if => //; last by skip; progress; smt.
  call (_ : 
  mem (StaticRev (G5.pk_guess_val)) G5.evs,
  G4.evs{1} = G5.evs{2} /\
  G4.test{1} = G5.test{2} /\
  G4.mSk{1} = G5.mSk{2} /\
  G4.mEexp{1} = G5.mEexp{2} /\
  G4.mStarted{1} = G5.mStarted{2} /\ 
  G4.mCompleted{1} = G5.mCompleted{2} /\
  G4.h2_queries{1} = G5.h2_queries{2} /\
  G4.test_sidx{1} = G5.test_sidx{2} /\
  G4.bad{1} = G5.bad{2}) => //.
  by apply A_ll.
  fun.
  seq 1 1:
(! mem (StaticRev G5.pk_guess_val{2}) G5.evs{2} /\
  ={i, a, r} /\ r{1} = None /\
  G4.evs{1} = G5.evs{2} /\
  G4.test{1} = G5.test{2} /\
  G4.mSk{1} = G5.mSk{2} /\
  G4.mEexp{1} = G5.mEexp{2} /\
  G4.mStarted{1} = G5.mStarted{2} /\
  G4.mCompleted{1} = G5.mCompleted{2} /\
  G4.h2_queries{1} = G5.h2_queries{2} /\
  G4.test_sidx{1} = G5.test_sidx{2} /\ G4.bad{1} = G5.bad{2}).
  wp; skip; progress.
  if => //.
  wp; skip; progress.
  intros => &2 h; fun; wp; skip; progress.
  intros => &1; fun; wp; skip; progress.
   by rewrite mem_cons; right.  

  fun; sp; if => //; if => //; wp; try rnd; skip; progress.
  intros => &2 h; fun; sp; if => //; wp; 
   if => //; wp; rnd; skip; progress.
   rewrite -lossless_sample_Eexp /Distr.weight;
    apply Distr.mu_eq.
   by rewrite /Fun.(==) /Fun.cpTrue /=.
 intros => &1; fun; sp; if => //; 
  if => //; wp; try rnd; skip; progress.
  rewrite -lossless_sample_Eexp /Distr.weight.
    apply Distr.mu_eq.
rewrite /Fun.(==) /Fun.cpTrue /= => x; rewrite mem_cons; smt.
 rewrite mem_cons; smt.
 
 fun; if => //; wp; skip; progress.
  intros => &2 h; fun; wp; skip; progress.
  intros => ?  
