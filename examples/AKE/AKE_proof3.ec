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

declare module A : Adv3{ AKE_eqS}.

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
       if (mem (StaticRev (psid_actor (compute_psid mStarted mEexp i))) evs) {
        if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
          r = mEexp.[i];
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

pred bad_eph_query (evs : Event list) =
exists j, exists A, exists B, exists X, exists r, 
0 <= j /\
nth evs j = Some (EphemeralRev(A,B,X,r)) /\
(forall k, j < k < length evs => nth evs k <> Some (StaticRev A)).

lemma bad_eph_query_mon : 
forall evs e,
bad_eph_query evs => 
bad_eph_query (e:: evs).
proof.
 intros => evs e [j] A B X r [hle] [h] hnot.
 exists (j+1);exists A; exists B; exists X; exists r.
 rewrite !nth_consN; first smt.
 rewrite (_ : j + 1 - 1 = j) ?h /=; first smt.
 split; first smt.
  progress => //.
  rewrite nth_consN; first smt.
  by apply hnot; generalize H0; rewrite length_cons; smt.
save.



local equiv Eq1 : AKE_eqS(A).main ~ G1(A).main : true ==> 
(AKE_eqS.h2_queries{1} = G1.h2_queries{2} /\
 AKE_eqS.test_sidx{1} = G1.test_sidx{2} /\ 
 AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2}) \/ bad_eph_query G1.evs{2}.
proof.
 fun.
 seq 16 16:
(AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.test{1} = G1.test{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2} /\
 AKE_eqS.h2_queries{1} = G1.h2_queries{2} /\
 AKE_eqS.test_sidx{1} = G1.test_sidx{2} /\
 ={pks}).
eqobs_in.
if => //.
call (_ : bad_eph_query G1.evs, 
 AKE_eqS.evs{1} = G1.evs{2} /\
 AKE_eqS.test{1} = G1.test{2} /\
 AKE_eqS.mSk{1} = G1.mSk{2} /\
 AKE_eqS.mEexp{1} = G1.mEexp{2} /\
 AKE_eqS.mStarted{1} = G1.mStarted{2} /\ 
 AKE_eqS.mCompleted{1} = G1.mCompleted{2}).
apply A_ll.
fun.
seq 1 1:
(! bad_eph_query G1.evs{2} /\
  ={i, a, r} /\
  AKE_eqS.evs{1} = G1.evs{2} /\
  AKE_eqS.test{1} = G1.test{2} /\
  AKE_eqS.mSk{1} = G1.mSk{2} /\
  AKE_eqS.mEexp{1} = G1.mEexp{2} /\
  AKE_eqS.mStarted{1} = G1.mStarted{2} /\
  AKE_eqS.mCompleted{1} = G1.mCompleted{2} /\
  r{2} = None).
by wp.
if => //.
seq 1 1:
((! bad_eph_query (tl G1.evs{2}) /\
   ={i, a, r} /\
   AKE_eqS.evs{1} = G1.evs{2} /\
   AKE_eqS.test{1} = G1.test{2} /\
   AKE_eqS.mSk{1} = G1.mSk{2} /\
   AKE_eqS.mEexp{1} = G1.mEexp{2} /\
   AKE_eqS.mStarted{1} = G1.mStarted{2} /\
   AKE_eqS.mCompleted{1} = G1.mCompleted{2} /\ r{2} = None) /\
  in_dom i{1} AKE_eqS.mStarted{1} /\ 
 (exists evs', G1.evs{2} = 
  EphemeralRev (compute_psid G1.mStarted G1.mEexp i){2} :: evs' )).
by wp; skip; progress; rewrite ?tl_cons //; exists G1.evs{2}.
if{2}.
wp; skip; progress => //.
conseq (_ : _ ==> bad_eph_query G1.evs{2}).
 smt.
 wp.
 wp; progress; skip; progress => //.
 generalize H1.
 elim /tuple4_ind (compute_psid G1.mStarted{2} G1.mEexp{2} i{2}) => A B X r htuple h.
 exists 0; exists A; exists B; exists X; exists r.
 rewrite nth_cons0; progress.
  rewrite nth_consN; first smt.
 apply not_def => h0; generalize h;rewrite /psid_actor /=.
 rewrite mem_cons; right.
 rewrite -(proj_some (StaticRev A)) -h0; apply nth_mem.
 smt.
 generalize H2; rewrite length_cons; smt.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial.
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 by fun; wp.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 fun.
 wp; trivial; skip; progress; smt.
 by intros => ? ?; fun; wp; trivial. 
 by intros => ?; fun; wp; skip; progress; apply bad_eph_query_mon.
 skip; progress => //; smt.
save.

local lemma Pr1 &m :
Pr[AKE_eqS(A).main() @ &m :
(in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs)] <=
Pr[G1(A).main() @ &m :
(in_dom G1.test_sidx G1.mCompleted /\
List.mem
(get_string_from_id G1.test_sidx G1.mStarted 
  G1.mCompleted G1.mEexp G1.mSk) 
(G1.h2_queries) /\
fresh_op (compute_sid G1.mStarted G1.mEexp G1.mCompleted G1.test_sidx) G1.evs)] +
Pr[G1(A).main() @ &m : bad_eph_query G1.evs].
proof.
apply (Real.Trans _ 
Pr[G1(A).main() @ &m :
   in_dom G1.test_sidx G1.mCompleted /\
   mem
     (get_string_from_id G1.test_sidx G1.mStarted G1.mCompleted G1.mEexp
        G1.mSk) G1.h2_queries /\
   fresh_op (compute_sid G1.mStarted G1.mEexp G1.mCompleted G1.test_sidx)
     G1.evs \/ bad_eph_query G1.evs] _ ).
equiv_deno Eq1 => //; smt.
rewrite Pr mu_or.
cut h: forall (a b c : real), 0%r <= c => a + b - c <= a + b by smt.
apply h; smt.
save.