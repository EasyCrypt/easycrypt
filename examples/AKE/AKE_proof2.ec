require import Option.
require import List.
require import Map.
require import FSet.
require import Int.
require import AKE_defs.
require import Real.

(* { Hello *)
(* dsfadfsdfdsf *)
(* } *)

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
  fun choose(s : Pk list) : Sidx 
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
    
  fun init() : unit = {
    evs = [];
    test = None;
    cSession = 0;
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
      if (in_dom A mSk && in_dom B mSk
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
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    
    init();
    while (i < qAgent) {
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

(* first we enforce no collisions on Init1 and Resp *)

pred collision_eexp_eexp(m : (Sidx, Eexp) map) =
  exists i j, in_dom i m /\ m.[i] = m.[j] /\ i <> j.

pred collision_eexp_rcvd(evs : Event list) =
  exists (i : int) (j : int) s1 s2 s3,
     0 <= i /\ 0 <= j /\ i < length evs /\
     i > j /\  nth evs i = Some (Accept s1) /\
     (   (nth evs j  = Some (Start s2)  /\ psid_sent s2 = sid_rcvd s1)
      \/ (nth evs j  = Some (Accept s3) /\ sid_sent s3 = sid_rcvd s1 /\ sid_role s3 = resp)).

lemma collision_eexp_rcvd_mon :
forall e evs,
 collision_eexp_rcvd evs =>
 collision_eexp_rcvd (e::evs).
proof.
 intros => e evs [i] j s1 ps1 s2 [hposi][hposj][hlen][hlt][hevi] hor.
 exists (i+1); exists (j+1); exists s1;exists ps1;
  exists s2;elim hor;intros => [hevj heq];do !split => //;first 2 by smt.
  by rewrite length_cons; smt.
  by smt.
  by rewrite -hevi nth_consN; smt.
  by left; do!split => //;rewrite -hevj nth_consN; smt.
  by smt.
  by smt.
  by rewrite length_cons; smt.
  by smt.
  by rewrite -hevi nth_consN; smt.
  by elim heq => heq1 heq2;right; do!split => //;rewrite -hevj nth_consN; smt.
save. 

pred no_start_coll (evs : Event list) =
forall X A1 A2 B1 B2 r1 r2 i j,
0 <= i =>
0 <= j =>
nth evs i = Some (Start (A1, B1, X, r1)) =>
nth evs j = Some (Start (A2, B2, X, r2)) =>
i = j.

lemma start_coll_mon : 
forall e evs,
! no_start_coll (evs) =>
! no_start_coll (e::evs).
proof.
 intros => e evs.
 cut h : no_start_coll (e::evs) => no_start_coll (evs); last by smt.
 rewrite /no_start_coll => hnocoll X A1 A2 B1 B2 r1 r2 i j hposi hposj hith hjth.
 cut heq := hnocoll X A1 A2 B1 B2 r1 r2 (i+1) (j+1) _ _ _ _; first 2 by smt.
 rewrite -hith nth_consN; smt.
 rewrite -hjth nth_consN; smt.  
 by smt.
save.

pred no_accept_coll (evs : Event list) =
forall X A1 A2 B1 B2 Y1 Y2 r1 r2 i j,
0 <= i < length evs =>
0 <= j < length evs =>
nth evs i = Some (Accept (A1, B1, X, Y1, r1)) =>
nth evs j = Some (Accept (A2, B2, X, Y2, r2)) =>
i = j.


pred valid_accepts evs =
  forall s i,
  0 <= i < length evs =>
  nth evs i = Some (Accept s) =>
  sid_role s = init => 
  exists j, i < j /\ j < length evs /\ nth evs j = Some (Start (psid_of_sid s)).



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


lemma nosmt fresh_eq_notfresh(t : Sid) (evs : Event list) :
  (! fresh t evs) =
  (notfresh t evs).
proof.
by elim /tuple5_ind t => ? ? ? ? ? heq;clear t heq;rewrite /fresh/notfresh /=; smt.
save.

lemma role_case : forall s, s = init \/ s = resp by smt.

lemma coll_fresh : 
forall e evs s,
List.mem (Accept s) evs =>
!collision_eexp_rcvd(e::evs) =>
no_start_coll(e::evs) =>
no_accept_coll(e::evs) =>
valid_accepts (e::evs) =>
!fresh s evs =>
!fresh s (e::evs).
proof.
 intros => e evs s hmem hcoll hnostartcoll hnacceptcoll hvalid.
 rewrite !fresh_eq_notfresh => hnfresh.
 elim (mem_nth (Accept s) evs _) => // i [hleq] hnth.
 apply not_fresh_imp_notfresh.
 elim /tuple5_ind s => A B X Y r;progress.
 rewrite /fresh /cmatching /psid_of_sid /=.
 apply not_def => [[hnorev]][hnoboth][hnorev_match] h.
 generalize hnfresh; rewrite /notfresh/cmatching /psid_of_sid /=.
 apply not_def => [ [hcase |[[hl hr] | [|]]]].
  by generalize hnorev; rewrite mem_cons not_or; smt.
  by generalize hnoboth; rewrite !not_and => [|]; rewrite mem_cons not_or; smt.
  by generalize hnorev_match; rewrite mem_cons not_or; smt.
  intros => [hsrev] [|]; last first.
    elim (h _); first by rewrite mem_cons; smt.
    by intros hor; rewrite mem_cons; smt.
    
    intros => [hnoacc] [hnostart|].

    elim (h _); first by rewrite mem_cons; smt.
    intros => [|].
    rewrite !mem_cons !not_or => [heq1 |hmem1]; last by smt.
    intros => [h0 hnoephm] {h0}.
  elim (role_case r) => hrole.
  cut _ : collision_eexp_rcvd (e :: evs); last by smt.
 pose s1 := (A, B, X, Y, init).
 exists (i+1);exists 0; exists s1; exists (psid_of_sid s1); 
  exists (cmatching s1); do !split => //; first by smt.
  rewrite length_cons; smt.
  by smt.
  rewrite /s1 -hrole -hnth nth_consN; first 2 by smt.
  by right;rewrite nth_cons0 /s1 /cmatching /sid_sent /sid_rcvd /sid_role/=; smt.
  elim (hvalid (B, A, Y, X, ! resp) 0 _ _);rewrite // ?nth_cons0 -heq1 ?hrole //=.
    by rewrite length_cons; smt.
  intros => j.
  apply not_def => [[hjpos]].
  rewrite (_ : j = (j-1) + 1) ?nth_consN /psid_of_sid /=; first 2 by smt.
  apply not_def => [[hlength]] heq.
  cut _ : mem (Start (B, A, Y, ! r)) evs; last by smt.
  rewrite hrole -(proj_some  (Start (B, A, Y, ! resp))) -heq.
  by apply nth_mem; generalize hlength; rewrite length_cons; smt.
 
  intros => [hstart] hnex hnoeph.
  elim (h _); first by rewrite mem_cons; smt. 
    intros => [|].
    rewrite !mem_cons !not_or => [heq1 |hmem1]; last by smt.
    intros => [h0 hnoephm].
    cut _: (exists (z : Epk), mem (Accept (B, A, Y, z, ! r)) (e :: evs)); last by smt.
    by exists X;rewrite heq1; smt.
    intros => [h0 hnoex] hnoephm.
    generalize hstart; rewrite mem_cons => [heq |]; last by smt.
 cut _ : collision_eexp_rcvd (e :: evs); last by smt.
 pose s1 := (A, B, X, Y, r).
 exists (i+1);exists 0; exists s1; exists (psid_of_sid (cmatching s1)); 
  exists (cmatching s1); do !split => //; first by smt.
  by rewrite length_cons; smt.
  by smt.
  rewrite /s1 -hnth nth_consN; first 2 by smt.
  by left;rewrite nth_cons0 /s1 /sid_rcvd /psid_of_sid /cmatching /psid_sent -heq /= /sid_role/=; smt.
  intros => [Z] haccZ.
  elim (h _); first by rewrite mem_cons; smt. 
    intros => [|].
    rewrite !mem_cons !not_or => [heq1 |hmem1]; last by smt.
    intros => [h0 hnoephm] {h0}.
    elim (mem_nth  (Accept (B, A, Y, Z, ! r)) evs _) => // k [hbounds] hjth.
    cut _ : 0 = k+1; last by smt.
     apply (hnacceptcoll Y B B A A X Z (!r) (!r) 0 (k+1)); first by smt.
     by rewrite length_cons; smt.
     by rewrite -heq1 nth_cons0.
     by rewrite -hjth nth_consN; smt.  
   intros => [_ habs].
   cut _: (exists (z : Epk), mem (Accept (B, A, Y, z, ! r)) (e :: evs)); last by smt.
   by exists Z; rewrite mem_cons; right; assumption.
save.

 
module AKE_NoColl(FA : Adv2) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
    
  fun init() : unit = {
    evs = [];
    test = None;
    cSession = 0;
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
      if (in_dom A mSk && 
         in_dom B mSk && !in_dom i mStarted &&
         ! collision_eexp_rcvd_op(Start((A,B,gen_epk(proj mEexp.[i]),init))::evs)){
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
      if (in_dom A mSk && in_dom B mSk
          && !in_dom i mStarted && !in_dom i mCompleted &&
         ! collision_eexp_rcvd_op(Accept((B,A,gen_epk(proj mEexp.[i]),X,resp))::evs)) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
      ! collision_eexp_rcvd_op(Accept(compute_sid mStarted mEexp mCompleted.[i <- Y] i)::evs)) {
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
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    
    init();
    while (i < qAgent) {
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
    }
    return (b = b');
  }
}.

(*{ proof: adding the collision check *)

section.
declare module A : Adv2{ AKE_EexpRev,AKE_NoColl}.

axiom A_Lossless_guess : 
forall (O <: AKE_Oracles2{A}),
  islossless O.eexpRev =>
  islossless O.h2_a =>
  islossless O.init1 =>
  islossless O.init2 =>
  islossless O.resp =>
  islossless O.staticRev => islossless O.sessionRev => islossless A(O).guess.

axiom A_Lossless_choose : 
forall (O <: AKE_Oracles2{A}),
  islossless O.eexpRev =>
  islossless O.h2_a =>
  islossless O.init1 =>
  islossless O.init2 =>
  islossless O.resp =>
  islossless O.staticRev => islossless O.sessionRev => islossless A(O).choose.


pred test_fresh(t : Sid option, evs : Event list) =
  t <> None /\ fresh (proj t) evs.

equiv Eq_AKE_EexpRev_AKE_no_collision :
 AKE_NoColl(A).main ~ AKE_EexpRev(A).main  :
={glob A} ==> 
(res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)){2}
=>
(res /\ test_fresh AKE_NoColl.test AKE_NoColl.evs
                    /\ ! collision_eexp_eexp(AKE_NoColl.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoColl.evs) ){1}.
proof.
 fun.
 seq 14 14:
(={glob A,b,pks,t_idx,key,keyo,b',i,pks} /\
   AKE_EexpRev.evs{2} = AKE_NoColl.evs{1} /\
   AKE_EexpRev.test{2} = AKE_NoColl.test{1} /\
   AKE_EexpRev.cSession{2} = AKE_NoColl.cSession{1} /\
   AKE_EexpRev.cH2{2} = AKE_NoColl.cH2{1} /\
   AKE_EexpRev.mH2{2} = AKE_NoColl.mH2{1} /\
   AKE_EexpRev.sH2{2} = AKE_NoColl.sH2{1} /\
   AKE_EexpRev.mSk{2} = AKE_NoColl.mSk{1} /\
   AKE_EexpRev.mEexp{2} = AKE_NoColl.mEexp{1} /\
   AKE_EexpRev.mStarted{2} = AKE_NoColl.mStarted{1} /\
   AKE_EexpRev.mCompleted{2} = AKE_NoColl.mCompleted{1}); first by eqobs_in.
if{1}; last first.
(* there is a collision: just show preservation on the right *)
conseq ( _ : collision_eexp_eexp_op AKE_EexpRev.mEexp{2} ==>
             collision_eexp_eexp_op AKE_EexpRev.mEexp{2})=> //.
 by smt.
 cut bhsh2: bd_hoare [ AKE_EexpRev(A).O.h2 : 
     collision_eexp_eexp_op AKE_EexpRev.mEexp ==>
     collision_eexp_eexp_op AKE_EexpRev.mEexp ] = 1%r;
 first by fun; wp; rnd => //; apply  TKey.Dword.lossless.
 cut bhsck2 : 
bd_hoare [ AKE_EexpRev(A).O.computeKey : 
     collision_eexp_eexp_op AKE_EexpRev.mEexp ==>
     collision_eexp_eexp_op AKE_EexpRev.mEexp ] = 1%r;
 first by fun; sp; if => //; wp; call bhsh2; wp.

 seq 0 2: (collision_eexp_eexp_op AKE_EexpRev.mEexp{2}).
  rnd{2}.
  call{2} (_ : collision_eexp_eexp_op AKE_EexpRev.mEexp ==>
               collision_eexp_eexp_op AKE_EexpRev.mEexp).
   fun (collision_eexp_eexp_op AKE_EexpRev.mEexp) => //.
 by apply A_Lossless_choose.
 by fun; wp.
 by fun; sp; if => //; wp; call bhsh2; wp.
 by fun; sp; if => //; wp.
 by fun; if; wp.  
 by fun; sp; if => //; wp.
 by fun; wp.
 by fun; sp; if => //; call bhsck2; wp.
  by skip; smt.
 
 if{2} => //; sp.
  call{2} (_ : collision_eexp_eexp_op AKE_EexpRev.mEexp ==>
               collision_eexp_eexp_op AKE_EexpRev.mEexp).
  fun (collision_eexp_eexp_op AKE_EexpRev.mEexp) => //.
 by apply A_Lossless_guess.
 by fun; wp.
 by fun; sp; if => //; wp; call bhsh2; wp.
 by fun; sp; if => //; wp.
 by fun; if; wp.  
 by fun; sp; if => //; wp.
 by fun; wp.
 by fun; sp; if => //; call bhsck2; wp.
 by if{2};[ call{2} bhsck2 => // | wp; rnd{2}; skip]; smt.

 seq 2 2:
(!collision_eexp_rcvd AKE_EexpRev.evs{2} =>
 ={b,pks,t_idx,key,keyo,b',i,pks,glob A} /\
  AKE_EexpRev.evs{2} = AKE_NoColl.evs{1} /\
  AKE_EexpRev.test{2} = AKE_NoColl.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_NoColl.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_NoColl.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_NoColl.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_NoColl.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_NoColl.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_NoColl.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_NoColl.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_NoColl.mCompleted{1}).
rnd.
call 
(_ :
  (collision_eexp_rcvd AKE_EexpRev.evs),
  (AKE_EexpRev.evs{2} = AKE_NoColl.evs{1} /\
  AKE_EexpRev.test{2} = AKE_NoColl.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_NoColl.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_NoColl.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_NoColl.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_NoColl.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_NoColl.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_NoColl.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_NoColl.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_NoColl.mCompleted{1})) => //.
 by apply A_Lossless_choose.
 by fun; wp; skip; smt.
 by intros=> &2 hcoll; fun; wp; skip; smt.
 by intros=> &1; fun; wp; skip; smt.
 
 by fun; sp; if => //;inline AKE_NoColl(A).O.h2 AKE_EexpRev(A).O.h2; wp; rnd;
   wp; skip; smt.
 by intros => &2 hcoll; fun; sp; if => //; inline AKE_NoColl(A).O.h2; wp; rnd; 
   try apply TKey.Dword.lossless; wp; skip; smt.
 by intros &1; fun; inline AKE_EexpRev(A).O.h2; sp; if => //; wp; rnd;
   try apply TKey.Dword.lossless; wp; skip; smt.

 fun; sp; if{1} => //.
 rcondt{2} 1 => //.
 wp; skip; smt.
 if{2} => //; conseq (_ : collision_eexp_rcvd_op 
                          (Start (A, B, gen_epk (proj AKE_EexpRev.mEexp.[i]), init){2} 
                            ::AKE_EexpRev.evs{2}) ==> 
                          collision_eexp_rcvd AKE_EexpRev.evs{2}) => //;
   first 2 by smt.
  wp; skip; progress.
  by rewrite -collision_eexp_rcvd_op_def.
  by intros => &2 hcoll; fun; wp.
  by intros => &2; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.

 fun.
 if{1}.
  by rcondt{2} 1 => //; wp; skip => //.
  if{2} => //.
  conseq 
(_ :  collision_eexp_rcvd_op (Accept
  (compute_sid AKE_EexpRev.mStarted AKE_EexpRev.mEexp 
   AKE_EexpRev.mCompleted.[i{2} <- Y{2}] i):: AKE_EexpRev.evs){2}  ==>  
   collision_eexp_rcvd AKE_EexpRev.evs{2}) => //;first 2 by smt.
  wp; skip; progress.
  by rewrite -collision_eexp_rcvd_op_def.
 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.
 
 fun; sp; if{1} => //.
 rcondt{2} 1 => //.
 wp; skip; smt.
 if{2} => //.
 conseq 
(_ : collision_eexp_rcvd_op 
 (Accept (B, A, gen_epk (proj AKE_EexpRev.mEexp.[i]), X, resp)
  :: AKE_EexpRev.evs){2} ==>
 collision_eexp_rcvd AKE_EexpRev.evs{2});first 2 by smt.
 by wp; skip; progress => //;rewrite -collision_eexp_rcvd_op_def.

 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.

 by fun; wp; skip; progress; smt.
 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; smt.
 
 by fun; inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2
  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;do 2!(sp; try if) => //;
  wp; try rnd; wp; skip; progress => //; smt.

 by intros => _ _; fun; inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
  sp; if => //; sp; if; wp; try rnd; try apply TKey.Dword.lossless; wp; skip; progress.
 
 by intros => _; fun; inline AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2; 
  sp; if => //; sp; if; wp; try rnd; try apply TKey.Dword.lossless; wp; skip; progress;
  apply collision_eexp_rcvd_mon.
  skip; smt.
 case (collision_eexp_rcvd AKE_EexpRev.evs{2}).
 conseq (_ :   collision_eexp_rcvd AKE_EexpRev.evs{2} ==> 
  collision_eexp_rcvd AKE_EexpRev.evs{2}) => //.
 smt.
if{1};if{2} => //.
call{1} (_ : true ==> true).
fun (true) => //; try (by fun; wp => //).
  by apply A_Lossless_guess.
  by fun; inline AKE_NoColl(A).O.h2; do 2!(sp; try if => //); wp; rnd;
    try apply TKey.Dword.lossless; skip; smt.
  by fun; inline  AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
    do 2!(sp; try if => //); wp; try rnd;
    try apply TKey.Dword.lossless; wp; skip; smt.
call{2} (_ : collision_eexp_rcvd AKE_EexpRev.evs ==>
             collision_eexp_rcvd AKE_EexpRev.evs).
fun (collision_eexp_rcvd AKE_EexpRev.evs) => //; try (by fun; wp => //; skip; smt).
  by apply A_Lossless_guess.
  by fun; inline AKE_EexpRev(A).O.h2; do 2!(sp; try if => //); wp; rnd;
    try apply TKey.Dword.lossless; skip; smt.
  by fun; inline  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;
    do 2!(sp; try if => //); wp; try rnd;
    try apply TKey.Dword.lossless; wp; skip; smt.
 sp; if{1}; if{2} => //.
  by inline AKE_NoColl(A).O.computeKey AKE_EexpRev(A).O.computeKey
            AKE_NoColl(A).O.h2 AKE_EexpRev(A).O.h2;
  sp; if{1}; if{2} => //; wp; try rnd; try rnd{1}; try rnd{2}; wp; skip; smt.
  by inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
  sp; if{1} => //; wp; try rnd; try rnd{1}; try rnd{2}; wp; skip; smt.
  by inline  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;
  sp; if{2} => //; wp; try rnd; try rnd{1}; try rnd{2}; wp; skip; smt.
  by wp; rnd; skip; smt.
call{1} (_ : true ==> true).
fun (true) => //; try (by fun; wp => //).
  by apply A_Lossless_guess.
  by fun; inline AKE_NoColl(A).O.h2; do 2!(sp; try if => //); wp; rnd;
    try apply TKey.Dword.lossless; skip; smt.
  by fun; inline  AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
    do 2!(sp; try if => //); wp; try rnd;
    try apply TKey.Dword.lossless; wp; skip; smt.
sp; if{1} => //.
  by inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
  sp; if{1} => //; wp; try rnd; try rnd{1}; try rnd{2}; wp; skip; smt.
  by wp; rnd{1}; skip; smt.
call{2} (_ : collision_eexp_rcvd AKE_EexpRev.evs ==>
             collision_eexp_rcvd AKE_EexpRev.evs).
fun (collision_eexp_rcvd AKE_EexpRev.evs) => //; try (by fun; wp => //; skip; smt).
  by apply A_Lossless_guess.
  by fun; inline AKE_EexpRev(A).O.h2; do 2!(sp; try if => //); wp; rnd;
    try apply TKey.Dword.lossless; skip; smt.
  by fun; inline  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;
    do 2!(sp; try if => //); wp; try rnd;
    try apply TKey.Dword.lossless; wp; skip; smt.
sp; if{2} => //.
  by inline  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;
  sp; if{2} => //; wp; try rnd; try rnd{1}; try rnd{2}; wp; skip; smt.
  by wp; rnd{2}; skip; smt.
 if => //;first by smt.
call 
(_ :
  (collision_eexp_rcvd AKE_EexpRev.evs),
  (AKE_EexpRev.evs{2} = AKE_NoColl.evs{1} /\
  AKE_EexpRev.test{2} = AKE_NoColl.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_NoColl.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_NoColl.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_NoColl.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_NoColl.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_NoColl.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_NoColl.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_NoColl.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_NoColl.mCompleted{1})) => //.
 by apply A_Lossless_guess.
 by fun; wp; skip; smt.
 by intros=> &2 hcoll; fun; wp; skip; smt.
 by intros=> &1; fun; wp; skip; smt.
 
 by fun; sp; if => //;inline AKE_NoColl(A).O.h2 AKE_EexpRev(A).O.h2; wp; rnd;
   wp; skip; smt.
 by intros => &2 hcoll; fun; sp; if => //; inline AKE_NoColl(A).O.h2; wp; rnd; 
   try apply TKey.Dword.lossless; wp; skip; smt.
 by intros &1; fun; inline AKE_EexpRev(A).O.h2; sp; if => //; wp; rnd;
   try apply TKey.Dword.lossless; wp; skip; smt.

 fun; sp; if{1} => //.
 rcondt{2} 1 => //.
 wp; skip; smt.
 if{2} => //; conseq (_ : collision_eexp_rcvd_op 
                          (Start (A, B, gen_epk (proj AKE_EexpRev.mEexp.[i]), init){2} 
                            ::AKE_EexpRev.evs{2}) ==> 
                          collision_eexp_rcvd AKE_EexpRev.evs{2}) => //;
   first 2 by smt.
  wp; skip; progress.
  by rewrite -collision_eexp_rcvd_op_def.
  by intros => &2 hcoll; fun; wp.
  by intros => &2; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.

 fun.
 if{1}.
  by rcondt{2} 1 => //; wp; skip => //.
  if{2} => //.
  conseq 
(_ :  collision_eexp_rcvd_op (Accept
  (compute_sid AKE_EexpRev.mStarted AKE_EexpRev.mEexp 
   AKE_EexpRev.mCompleted.[i{2} <- Y{2}] i):: AKE_EexpRev.evs){2}  ==>  
   collision_eexp_rcvd AKE_EexpRev.evs{2}) => //;first 2 by smt.
  wp; skip; progress.
  by rewrite -collision_eexp_rcvd_op_def.
 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.
 
 fun; sp; if{1} => //.
 rcondt{2} 1 => //.
 wp; skip; smt.
 if{2} => //.
 conseq 
(_ : collision_eexp_rcvd_op 
 (Accept (B, A, gen_epk (proj AKE_EexpRev.mEexp.[i]), X, resp)
  :: AKE_EexpRev.evs){2} ==>
 collision_eexp_rcvd AKE_EexpRev.evs{2});first 2 by smt.
 by wp; skip; progress => //;rewrite -collision_eexp_rcvd_op_def.

 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; progress => //; apply collision_eexp_rcvd_mon.

 by fun; wp; skip; progress; smt.
 by intros => &2 hcoll; fun; wp; skip; smt.
 by intros => &1; fun; wp; skip; smt.
 
 by fun; inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2
  AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2;do 2!(sp; try if) => //;
  wp; try rnd; wp; skip; progress => //; smt.

 by intros => _ _; fun; inline AKE_NoColl(A).O.computeKey AKE_NoColl(A).O.h2;
  sp; if => //; sp; if; wp; try rnd; try apply TKey.Dword.lossless; wp; skip; progress.
 
 by intros => _; fun; inline AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2; 
  sp; if => //; sp; if; wp; try rnd; try apply TKey.Dword.lossless; wp; skip; progress;
  apply collision_eexp_rcvd_mon.
 simplify.

 seq 2 2:
( ={keyo, b} /\
   ={glob A} /\
   AKE_EexpRev.evs{2} = AKE_NoColl.evs{1} /\
   AKE_EexpRev.test{2} = AKE_NoColl.test{1} /\
   AKE_EexpRev.cSession{2} = AKE_NoColl.cSession{1} /\
   AKE_EexpRev.cH2{2} = AKE_NoColl.cH2{1} /\
   AKE_EexpRev.mH2{2} = AKE_NoColl.mH2{1} /\
   AKE_EexpRev.sH2{2} = AKE_NoColl.sH2{1} /\
   AKE_EexpRev.mSk{2} = AKE_NoColl.mSk{1} /\
   AKE_EexpRev.mEexp{2} = AKE_NoColl.mEexp{1} /\
   AKE_EexpRev.mStarted{2} = AKE_NoColl.mStarted{1} /\
   AKE_EexpRev.mCompleted{2} = AKE_NoColl.mCompleted{1}).
 sp; if => //; first smt.
 inline AKE_NoColl(A).O.computeKey AKE_EexpRev(A).O.computeKey
            AKE_NoColl(A).O.h2 AKE_EexpRev(A).O.h2; sp; if; first by smt.
by wp; rnd; wp; skip => &1 &2 [[?][?][?][?][[testR][?][testL][?][[h]hnocoll]]];
  elim (h _) => //;progress; smt.
by wp; skip; progress; smt.
by wp; rnd; wp; skip; progress; smt.
by skip; progress => //;smt.
by skip; progress => //;smt.
save.



lemma Eq_AKE_EexpRev_AKE_no_collision_Pr &m :
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
Pr[AKE_NoColl(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)].
proof.
 admit.
save.
(* need symmetry rule for pRHL *)


(*end proof: adding the collision check }*)

(*{ enforcing freshness *)
(* first, we introduce an operator that implements
 the predicate fresh *)

op fresh_op : Sid -> Event list-> bool.

axiom fresh_op_def : forall s evs,
fresh s evs <=> fresh_op s evs = true.



local module AKE_Enforcement(FA : Adv2) = {
  
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
    
  fun init() : unit = {
    evs = [];
    test = None;
    cSession = 0;
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
      if (in_dom i mStarted && 
    (let evs' = EphemeralRev(compute_psid mStarted mEexp i)::evs
     in test <> None => fresh_op (proj test) evs' )) {
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
      if ( in_dom A mSk && 
         in_dom B mSk && !in_dom i mStarted &&
         ! collision_eexp_rcvd_op(Start((A,B,gen_epk(proj mEexp.[i]),init))::evs)) {
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
      if (in_dom A mSk && in_dom B mSk
          && !in_dom i mStarted && !in_dom i mCompleted &&
         ! collision_eexp_rcvd_op(Accept((B,A,gen_epk(proj mEexp.[i]),X,resp))::evs)) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
      ! collision_eexp_rcvd_op(Accept(compute_sid mStarted mEexp mCompleted.[i <- Y] i)::evs)) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk &&
      (let evs' = StaticRev A::evs
       in test <> None => fresh_op (proj test) evs' )) {
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
      if (in_dom i mCompleted &&
     (let evs' = SessionRev
          (compute_sid mStarted mEexp mCompleted i)::evs
     in test <> None => fresh_op (proj test) evs' )) {
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
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    
    init();
    while (i < qAgent) {
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
    }
    return (b = b');
  }
}.

(*{ Proof: enforcement doesn not make a difference
    when we have fresh in the event *)



lemma no_start_coll_pres : 
forall e evs, 
 (forall s, e <> Start s) =>
 no_start_coll evs =>
 no_start_coll (e :: evs).
proof.
 rewrite /no_start_coll; progress.
 cut _ :  0 <> i.
 apply not_def => heq.
 generalize heq H3 => <-; rewrite nth_cons0 => h.
 cut z:= H (A1, B1, X, r1).
 by generalize z; rewrite -(proj_some (Start (A1, B1, X, r1))) -h proj_some.
 cut _ : 0 <> j.
 apply not_def => heq.
 generalize heq H4 => <-; rewrite nth_cons0 => h.
 cut z:= H (A2, B2, X, r2).
 by generalize z; rewrite -(proj_some (Start (A2, B2, X, r2))) -h proj_some.
 cut _: i - 1 = j - 1;last by smt.
 apply (H0 X A1 A2 B1 B2 r1 r2 _ _ _ _ ); first 2 by smt.
 by rewrite -H3 nth_consN  //.
 by rewrite -H4 nth_consN  //.
save.


lemma mem_nth_simple x (xs : 'a list) j: 
nth xs j = Some x =>
List.mem x xs.
proof.
 intros => hjth.
 rewrite -(proj_some x) -hjth.
 apply nth_mem.
 cut: (! 0 <= j) => false; last by smt.
 intros => h; generalize hjth; rewrite nth_neg; smt.
 cut: (! j < length xs) => false; last by smt.
 intros => h;generalize hjth; rewrite nth_geq_len; smt.
qed.

lemma Some_inj :
forall (s1 s2 : 'a), Some s1 = Some s2 => s1 = s2 by smt. 

lemma no_start_coll_pres_ev : 
forall s evs, 
 no_start_coll evs =>
 (forall s', mem (Start s') evs => psid_sent s <> psid_sent s') => 
 no_start_coll (Start s :: evs).
proof.
 intros => s evs; rewrite /no_start_coll; progress.
 case (0 = i); case (0 = j) => // hj hi.

  generalize H3; rewrite -hi nth_cons0 => heq.
  generalize H4; rewrite nth_consN // => heq'.
  cut:= H0 (A2, B2, X, r2) _.
   apply (mem_nth_simple _ _ (j-1)) => //.
  cut -> : s =  (A1, B1, X, r1); 
   first by apply Start_inj; apply Some_inj; rewrite heq.
  by rewrite /psid_sent /=.

  generalize H4; rewrite -hj nth_cons0 => heq.
  generalize H3; rewrite nth_consN // => heq'.
  cut:= H0 (A1, B1, X, r1) _.
   apply (mem_nth_simple _ _ (i-1)) => //.
  cut -> : s =  (A2, B2, X, r2);  
    first by apply Start_inj; apply Some_inj; rewrite heq.
  by rewrite /psid_sent /=.

  generalize H3; rewrite nth_consN // => heq.
  generalize H4; rewrite nth_consN // => heq'.
  by cut := H X A1 A2 B1 B2 r1 r2 (i-1) (j-1) _ _ _ _; smt.
qed.

lemma no_accept_coll_pres : 
forall e evs, 
 (forall s, e <> Accept s) =>
 no_accept_coll evs =>
 no_accept_coll (e :: evs).
proof.
 rewrite /no_accept_coll; progress.
 cut _ :  0 <> i.
 apply not_def => heq.
 generalize heq H5 => <-; rewrite nth_cons0 => h.
 cut z:= H (A1, B1, X, Y1, r1).
 by generalize z; rewrite -(proj_some (Accept (A1, B1, X, Y1, r1))) -h proj_some.
 cut _ : 0 <> j.
 apply not_def => heq.
 generalize heq H6 => <-; rewrite nth_cons0 => h.
 cut z:= H (A2, B2, X, Y2, r2).
 by generalize z; rewrite -(proj_some (Accept (A2, B2, X, Y2, r2))) -h proj_some.
 cut _: i - 1 = j - 1;last by smt.
 apply (H0 X A1 A2 B1 B2 Y1 Y2 r1 r2 _ _ _ _ ).
 by generalize H2; rewrite length_cons; smt.
 by generalize H4; rewrite length_cons; smt.
 by rewrite -H5 nth_consN  //.
 by rewrite -H6 nth_consN  //.
save.

lemma no_accept_coll_pres_ev : 
forall s evs, 
 no_accept_coll evs =>
 (forall s', mem (Accept s') evs => sid_sent s <> sid_sent s') => 
 no_accept_coll (Accept s :: evs).
proof.
 intros => s evs; rewrite /no_accept_coll; progress.
 case (0 = i); case (0 = j) => // hj hi.
 
  generalize H5; rewrite -hi nth_cons0 => heq.
  generalize H6; rewrite nth_consN // => heq'.
  cut:= H0 (A2, B2, X, Y2, r2) _. 
   apply (mem_nth_simple _ _ (j-1)) => //.
  cut -> : s =  (A1, B1, X, Y1, r1); 
   first by apply Accept_inj; apply Some_inj; rewrite heq.
  by rewrite /sid_sent /=.

  generalize H5; rewrite nth_consN // => heq'.
  generalize H6; rewrite -hj nth_cons0 => heq.
  cut:= H0 (A1, B1, X, Y1, r1) _.
   apply (mem_nth_simple _ _ (i-1)) => //.
  cut -> : s =  (A2, B2, X, Y2, r2);  
    first by apply Accept_inj; apply Some_inj; rewrite heq.
  by rewrite /sid_sent /=.

  generalize H5; rewrite nth_consN // => heq.
  generalize H6; rewrite nth_consN // => heq'.
  cut := H X A1 A2 B1 B2 Y1 Y2 r1 r2 (i-1) (j-1) _ _ _ _; last 3 by smt.
   by generalize H1 H2; rewrite length_cons; smt. 
   by generalize H3 H4; rewrite length_cons; smt.
save.

lemma n_exp_recvd_coll :
 forall e evs,
(forall ps, e <> Start ps) =>
(forall s, e <> Accept s) =>
! collision_eexp_rcvd evs => 
! collision_eexp_rcvd (e :: evs). 
proof.
 intros => e evs hnstrt hnacc hcoll.
 rewrite /collision_eexp_rcvd /=. 
 apply not_def => [[i]] j s1 s2 s3 [hposi][hposj][hlength][hlt][hith] hor.
 cut h: 0 <> i.
  apply not_def => heq.
  by generalize hith; rewrite -heq nth_cons0; smt.

 cut h': 0 <> j.
  apply not_def => heq.
 generalize hor; rewrite -heq nth_cons0 => [[heq'] _ |[heq'] _ ].
  cut abs := hnstrt s2.
 by generalize abs;rewrite -(proj_some (Start s2)) -heq' proj_some.
  by cut h' := hnacc s3; generalize h'; rewrite -(proj_some e) heq' proj_some.
 cut: collision_eexp_rcvd evs; last by smt.
 exists (i-1); exists (j-1); exists s1; exists s2; exists s3; progress; first 2 by smt.
 by generalize hlength; rewrite length_cons; smt.
 by smt.
 by generalize hith; rewrite nth_consN; smt.
 by generalize hor; rewrite nth_consN; smt. 
save.

pred start_evs_eexps evs (mEexps : (Sidx, Eexp) map) =
forall s,  
List.mem (Start s) evs => 
exists e,
in_dom e mEexps /\
psid_sent s = gen_epk (proj (mEexps.[e])).

lemma start_evs_eexps_emp : 
forall m,
start_evs_eexps [] m.
proof.
 intros => m; rewrite /start_evs_eexps; smt.
save.

lemma start_evs_eexps_pres :
forall e evs m,
start_evs_eexps evs m =>
(forall s, e <> Start s) =>
start_evs_eexps (e::evs) m.
proof.
 intros e evs m; rewrite /start_evs_eexps  => htl hneq s; rewrite mem_cons => [|] hor.
 by cut _ := hneq s; smt.
 by apply htl.
save.

lemma start_evs_eexps_pres_ev :
forall evs m s,
start_evs_eexps evs m =>
(exists e, in_dom e m /\ psid_sent s = gen_epk (proj (m.[e]))) =>
start_evs_eexps (Start s::evs) m.
proof.
 intros => evs m s; rewrite /start_evs_eexps => htl hex s'; 
  rewrite mem_cons => [|] hor.
 by cut ->: s' = s by apply Start_inj => //.
 by apply htl. 
save.


pred accept_evs_eexps evs (mEexps : (Sidx, Eexp) map) =
forall s,  
List.mem (Accept s) evs => 
exists e,
in_dom e mEexps /\
sid_sent s = gen_epk (proj (mEexps.[e])).

lemma accept_evs_eexps_emp : 
forall m,
accept_evs_eexps [] m.
proof.
 intros => m; rewrite /accept_evs_eexps; smt.
save.


lemma accept_evs_eexps_pres :
forall e evs m,
accept_evs_eexps evs m =>
(forall s, e <> Accept s) =>
accept_evs_eexps (e::evs) m.
proof.
 intros e evs m; rewrite /accept_evs_eexps  => htl hneq s; rewrite mem_cons => [|] hor.
 by cut _ := hneq s; smt.
 by apply htl.
save.

lemma accept_evs_eexps_pres_ev :
forall evs m s,
accept_evs_eexps evs m =>
(exists e, in_dom e m /\ sid_sent s = gen_epk (proj (m.[e]))) =>
accept_evs_eexps (Accept s::evs) m.
proof.
 intros => evs m s; rewrite /accept_evs_eexps => htl hex s'; 
  rewrite mem_cons => [|] hor.
 by cut ->: s' = s by apply Accept_inj => //.
 by apply htl. 
save.


lemma valid_accept_pres : 
forall e evs, 
valid_accepts evs =>
(forall s, e <> Accept s) => 
valid_accepts (e::evs).
proof.
 intros => e evs; rewrite /valid_accepts => htl hnotacc s i hbnds hith hrole.
 case (0 = i) => hZ.
   generalize hZ hith => <-; rewrite nth_cons0 => heq.
   by cut h:= hnotacc s; generalize h; rewrite -(proj_some (Accept s)) -heq proj_some. 
   
   elim (htl s (i-1) _ _ _) => //.
    by generalize hbnds; rewrite length_cons; smt.
    by rewrite -hith nth_consN //.
   intros => j [hlt][hll] hjth.
   exists (j + 1); do split => //.
   smt.
   rewrite length_cons; smt.
   rewrite -hjth nth_consN.

cut _: !(i < 0).
apply not_def => hi; generalize hith; rewrite nth_neg //; smt.
smt.
smt.
save. 

lemma valid_accept_pres_ev : 
forall evs s, 
valid_accepts evs =>
mem (Start (psid_of_sid s)) evs =>
valid_accepts (Accept s::evs).
proof.
  intros => evs s; rewrite /valid_accepts => htl hmem s' i hbnds hith hrole.
  case (0 = i) => hZ.

   generalize hZ hith => <-; rewrite nth_cons0 => heq.
   cut heq': s = s'.  
    by apply Accept_inj;rewrite -(proj_some (Accept s)) heq proj_some.
   elim (mem_nth (Start (psid_of_sid s)) evs _) => // j [hbounds] hjth.
   exists (j+1); do !split => //.
    by smt.
    by rewrite length_cons; smt.
    by rewrite -heq' -hjth nth_consN; smt.

   elim (htl s' (i-1) _ _ _) => //.
   by generalize hbnds; rewrite length_cons; smt.
   by rewrite -hith nth_consN //.
   intros => j [hlt][hll] hjth.
   exists (j + 1); do split => //.
     by smt.
     by rewrite length_cons; smt.

     rewrite -hjth nth_consN.
     cut _: !(i < 0).
     apply not_def => hi; generalize hith; rewrite nth_neg //; smt.
     smt. 
     smt.
save.


lemma valid_accept_pres_ev2 : 
forall evs s, 
valid_accepts evs =>
sid_role s = resp =>
valid_accepts (Accept s::evs).
proof.
 intros => evs s hvalid hrole.
 rewrite /valid_accepts => s' i.
 case (0 = i).
  
  intros => <- hbnds; rewrite nth_cons0 => heq.
  generalize hrole.
  cut ->: s = s' by (apply Accept_inj; apply Some_inj => //); smt.
  
  intros => hneq; rewrite length_cons nth_consN // => h1 h2 h3.
  elim (hvalid s' (i-1) _ _ _) => //.
   by smt.
   intros => j [hlt][hbnds'] hnth.
   exists (j+1); progress => //; rewrite ?nth_consN; smt.
save.     
   
  
pred inv_started evs (mStarted : (Sidx, Sdata2) map)
                     (mEexp : (Sidx, Eexp) map)  =
forall ps, 
List.mem (Start ps) evs <=>
(exists i,
in_dom i mStarted /\
in_dom i mEexp /\
let (A, B, r) = proj (mStarted.[i]) in
ps = (A, B, gen_epk (proj mEexp.[i]), r) /\
r = init).

lemma inv_started_pres :
forall evs e m1 m2,
inv_started evs m1 m2 =>
(forall s, e <> Start s) =>
inv_started (e::evs) m1 m2.
proof.
 intros => evs e m1 m2; rewrite /inv_started => htl hnstsrt ps; 
  rewrite mem_cons; split.
   intros => [|] h.
    by cut:= hnstsrt ps; smt. 
    by cut [h1 hcl]:= htl ps => {hcl};apply h1.
 
   intros => [i][hdom1][hdom2] heq.
   cut [h1 hcl]:= htl ps => {h1}; right; apply hcl.
   exists i; progress => //.
   by generalize H heq => -> /=.
   by generalize H heq => -> /=.
save.

(*  intros => evs e m1 m2; rewrite /inv_started => htl hnstsrt ps;  *)
(*   rewrite mem_cons. *)
(*    intros => [|] h. *)
(*     by cut:= hnstsrt ps; smt.  *)
(*     by cut h1:= htl ps;apply h1. *)
(* save. *) 

lemma inv_started_pres_ev :
forall evs A0 B m1 m2 i ,
inv_started evs m1 m2 =>
in_dom i m2 =>
! in_dom i m1 =>
inv_started (Start (A0,B, gen_epk (proj m2.[i]), init)::evs) m1.[i <- (A0,B,init)] m2.
proof.
  intros => evs A0 B m1 m2 i; rewrite /inv_started => hinv hindom hnindom ps;
   rewrite mem_cons; split.
   intros => [heq|hmem].
   cut: ps = (A0, B, gen_epk (proj m2.[i]), init); first by apply Start_inj.
   intros => {heq} heq.
   exists i; progress => //; last 4 by generalize H; rewrite get_setE proj_some.
    by rewrite in_dom_setE.

   elim (hinv ps) => h1 h2.
   elim (h1 _) => //= i' [hindom2][hindom3 heq].
   cut hneq: i <> i'.
    by apply not_def => heq'; generalize heq' hindom2 hnindom => ->.
   exists i'; progress => //.
    by rewrite in_dom_set; smt.
    by generalize H heq; rewrite get_setNE // => -> /=.
    by generalize H heq; rewrite get_setNE // => -> /=.
   intros => [i'][hdom2][hdom3] heq.
   cut [[hl1 hl2]|hr]: ((i <> i' /\ in_dom i' m1) \/ i' = i).
    case (i' = i) => // h; generalize hdom2; rewrite in_dom_setNE => //; smt.
   right; cut:= hinv ps => [[hl']] hr'; apply hr'; exists i'; do !split => //.
   by generalize heq; rewrite get_setNE //;elim /tuple3_ind (proj m1.[i']).
   by left; generalize heq; rewrite hr get_setE proj_some => /= ->.
save.

(*
lemma inv_started_pres_ev2 :
forall evs A0 B m1 m2 i ,
inv_started evs m1 m2 =>
in_dom i m2 =>
! in_dom i m1 =>
inv_started (Start (A0,B, gen_epk (proj m2.[i]), resp)::evs) m1.[i <- (A0,B,resp)] m2.
proof.
  intros => evs A0 B m1 m2 i; rewrite /inv_started => hinv hindom hnindom ps;
   rewrite mem_cons; split.
   intros => [heq|hmem].
*)   


pred inv_accepted evs (mStarted : (Sidx, Sdata2) map) 
                      (mEexp : (Sidx, Eexp) map)
                      (mCompleted : (Sidx, Epk) map)  =
forall (ps : Sid),
List.mem (Accept ps) evs <=>
(exists (i : Sidx),
in_dom i mStarted /\
in_dom i mCompleted /\
in_dom i mEexp /\
ps = compute_sid mStarted mEexp mCompleted i).

lemma inv_accepted_pres :
forall evs e m1 m2 m3,
inv_accepted evs m1 m2 m3 =>
(forall s, e <> Accept s) =>
inv_accepted (e::evs) m1 m2 m3.
proof.
 intros => evs e m1 m2 m3; rewrite /inv_accepted => htl hnstsrt ps.
  rewrite mem_cons; split.
   intros => [|] h.
    by cut:= hnstsrt ps; smt. 
    by cut [h1 hcl]:= htl ps => {hcl};apply h1.
 
   intros => [i][hdom1][hdom2][hdom3] heq.
   cut [h1 hcl]:= htl ps => {h1}; right; apply hcl.
   exists i; progress => //.
save.


lemma inv_accepted_pres_ev2 :
forall evs e m1 m2 m3 i v,
inv_accepted evs m1 m2 m3 =>
!in_dom i m1 =>
!in_dom i m3 =>
(forall s, e <> Accept s) =>
inv_accepted (e::evs) m1.[i <- v] m2 m3.
proof.
 intros => evs e m1 m2 m3 i v; rewrite /inv_accepted => htl hnindom hnindom' hnstsrt ps.
  rewrite mem_cons; split.
   intros => [|] h.
    by cut:= hnstsrt ps; smt. 
    cut [h1 hcl]:= htl ps => {hcl}.
    cut := h1 _ => //.
    intros => [i'][hindom1][hindom2][hindom3] heq.
    cut hneq: i <> i'.
    by apply not_def => heq'; generalize heq' hnindom hindom1 => ->.
    exists i'; do !split => //.
     by rewrite in_dom_set; left.
     by rewrite /compute_sid get_setNE //.
 
  intros => [i'][hdom1][hdom2][hdom3] heq.
   cut [h1 hcl]:= htl ps => {h1}; right; apply hcl.
   cut [[hl1 hl2]|hr]: ((i <> i' /\ in_dom i' m1) \/ i' = i).
    generalize hdom1; rewrite in_dom_set => [hdom'|heq']; smt.
   exists i'; progress => //.
   by rewrite heq /compute_sid get_setNE //.
   by generalize hr hnindom' hdom2 => ->; smt.
save.

lemma inv_accepted_pres_ev1 :
forall evs m1 m2 m3 i Y,
inv_accepted evs m1 m2 m3 =>
in_dom i m1 =>
in_dom i m2 =>
! in_dom i m3 =>
inv_accepted (Accept (compute_sid m1 m2 m3.[i <- Y] i)::evs) m1 m2 
    m3.[i <- Y].
proof.
 intros => evs m1 m2 m3 i Y;
 rewrite /inv_accepted => htl hindom1 hindom2 hnindom ps;
 rewrite mem_cons; split.
  intros => [|] heq.
  rewrite (_ : ps = compute_sid m1 m2 m3.[i <- Y] i); first by apply Accept_inj.
  exists i; do !split => //.
   by rewrite in_dom_setE.
  cut [h1 h2] := htl ps.
  elim (h1 _) => //.
  intros => {h1}{h2} i' [hdom1] [hdom2] [hdom3] heq'.
   exists i'; do !split => //.
   by rewrite in_dom_set; smt.
   rewrite heq' /compute_sid /=.
   case (i = i') => heq''.
    by generalize heq'' hnindom hdom2 => ->; smt.
    by rewrite get_setNE //.
  
  intros => [i'][hdom1][hdom2][hdom3] ->.
   case (i' = i) => heq''.
   by rewrite heq''; left.
   right.
   cut [h1 h2] := htl (compute_sid m1 m2 m3.[i <- Y] i').
   apply h2 => // {h1}{h2}.
   exists i'; progress => //.
   generalize hdom2; rewrite in_dom_setNE //.
   by rewrite /compute_sid get_setNE; smt.
save.

axiom gen_epk_inj : forall e1 e2,
gen_epk e1 = gen_epk e2 =>
e1 = e2.


lemma proj_inj_some : 
forall (x y : 'a option),
x <> None => 
y <> None =>
proj x = proj y =>
x = y.
proof.
 intros => x y;elim /option_case_eq x => //;elim /option_case_eq y => //.
 by intros=> [x'] -> [y'] ->; rewrite !proj_some.
save.


local equiv Eq_AKE_EexpRev_AKE_Enforcement :
 AKE_Enforcement(A).main ~ AKE_NoColl(A).main  :
true ==> 
(res /\ test_fresh AKE_Enforcement.test AKE_Enforcement.evs
                    /\ ! collision_eexp_eexp(AKE_Enforcement.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Enforcement.evs) ){1} <=>
(res /\ test_fresh AKE_NoColl.test AKE_NoColl.evs
                    /\ ! collision_eexp_eexp(AKE_NoColl.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoColl.evs)){2}.
proof.
 fun.
 seq 14 14:(={b,pks,t_idx,key,keyo,b',i,pks} /\
  AKE_NoColl.evs{2} = AKE_Enforcement.evs{1} /\
  AKE_NoColl.test{2} = AKE_Enforcement.test{1} /\
  AKE_NoColl.cSession{2} = AKE_Enforcement.cSession{1} /\
  AKE_NoColl.cH2{2} = AKE_Enforcement.cH2{1} /\
  AKE_NoColl.mH2{2} = AKE_Enforcement.mH2{1} /\
  AKE_NoColl.sH2{2} = AKE_Enforcement.sH2{1} /\
  AKE_NoColl.mSk{2} = AKE_Enforcement.mSk{1} /\
  AKE_NoColl.mEexp{2} = AKE_Enforcement.mEexp{1} /\
  AKE_NoColl.mStarted{2} = AKE_Enforcement.mStarted{1} /\
  AKE_NoColl.mCompleted{2} = AKE_Enforcement.mCompleted{1} /\
  AKE_NoColl.evs{2} = [] /\ 
  (forall (s : Sidx), in_dom s AKE_NoColl.mEexp{2})).
 inline AKE_Enforcement(A).init AKE_NoColl(A).init.
 while
(  ={sidxs} /\
AKE_Enforcement.mEexp{1} = AKE_NoColl.mEexp{2}  /\
  (forall (s : Sidx), !mem s sidxs{2} => in_dom s AKE_NoColl.mEexp{2})). 
wp; rnd; wp; skip; progress; try smt.
case  (s = (pick sidxs{2})) => h.
 by rewrite h;apply in_dom_setE.
generalize H5; rewrite mem_rm !not_and => [hl|]; last by smt.
 by cut:= H s _ => //;rewrite in_dom_setNE //.
while (={pks} /\ AKE_Enforcement.mSk{1} = AKE_NoColl.mSk{2}).
by wp; rnd.
by wp; skip; progress => //; smt.
  if=> //.
   seq 2 2:(={b,pks,t_idx,key,keyo,b',i,pks} /\
  AKE_NoColl.evs{2} = AKE_Enforcement.evs{1} /\
  AKE_NoColl.test{2} = AKE_Enforcement.test{1} /\
  AKE_NoColl.cSession{2} = AKE_Enforcement.cSession{1} /\
  AKE_NoColl.cH2{2} = AKE_Enforcement.cH2{1} /\
  AKE_NoColl.mH2{2} = AKE_Enforcement.mH2{1} /\
  AKE_NoColl.sH2{2} = AKE_Enforcement.sH2{1} /\
  AKE_NoColl.mSk{2} = AKE_Enforcement.mSk{1} /\
  AKE_NoColl.mEexp{2} = AKE_Enforcement.mEexp{1} /\
  AKE_NoColl.mStarted{2} = AKE_Enforcement.mStarted{1} /\
  AKE_NoColl.mCompleted{2} = AKE_Enforcement.mCompleted{1} /\
  AKE_NoColl.evs{2} = [] /\ 
  (forall (s : Sidx), in_dom s AKE_NoColl.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_NoColl.mEexp{2}).
rnd.
call (_ :
   AKE_NoColl.evs{2} = AKE_Enforcement.evs{1} /\
  AKE_NoColl.test{2} = AKE_Enforcement.test{1} /\
  AKE_NoColl.cSession{2} = AKE_Enforcement.cSession{1} /\
  AKE_NoColl.cH2{2} = AKE_Enforcement.cH2{1} /\
  AKE_NoColl.mH2{2} = AKE_Enforcement.mH2{1} /\
  AKE_NoColl.sH2{2} = AKE_Enforcement.sH2{1} /\
  AKE_NoColl.mSk{2} = AKE_Enforcement.mSk{1} /\
  AKE_NoColl.mEexp{2} = AKE_Enforcement.mEexp{1} /\
  AKE_NoColl.mStarted{2} = AKE_Enforcement.mStarted{1} /\
  AKE_NoColl.mCompleted{2} = AKE_Enforcement.mCompleted{1} /\
  AKE_Enforcement.test{1} = None /\
  !collision_eexp_rcvd(AKE_NoColl.evs{2}) /\
  accept_evs_eexps AKE_NoColl.evs{2} AKE_NoColl.mEexp{2} /\
  start_evs_eexps AKE_NoColl.evs{2} AKE_NoColl.mEexp{2} /\
  no_start_coll(AKE_NoColl.evs{2}) /\
  no_accept_coll(AKE_NoColl.evs{2}) /\
  valid_accepts (AKE_NoColl.evs{2}) /\
  inv_started AKE_NoColl.evs{2} AKE_NoColl.mStarted{2} AKE_NoColl.mEexp{2}  /\
  inv_accepted AKE_NoColl.evs{2} AKE_NoColl.mStarted{2} 
             AKE_NoColl.mEexp{2} AKE_NoColl.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_NoColl.mEexp{2}) /\
! collision_eexp_eexp_op AKE_NoColl.mEexp{2} /\ 
  (forall x, in_dom x AKE_NoColl.mCompleted{2} => in_dom x AKE_NoColl.mStarted{2}) /\
  (forall x, in_dom x AKE_NoColl.mStarted{2} => !in_dom x AKE_NoColl.mCompleted{2} =>
     sd2_role (proj (AKE_NoColl.mStarted{2}.[x])) = init)).
   fun; wp; skip; progress => //.
    by apply n_exp_recvd_coll => //; smt.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  
    by smt.
    by smt.
    by apply H10.
    by apply n_exp_recvd_coll => //; smt.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.  
    by smt.
    by smt.
    by apply H10.
    by smt.
    by smt.
    by apply H10.

    fun; sp; (if; first smt);
    inline AKE_Enforcement(A).O.h2  AKE_NoColl(A).O.h2;
    wp; try rnd; wp; skip; [smt | 
    intros => &1 &2 H1; do!split; smt].


   fun; sp; (if; first by smt); wp; skip; progress; last 12 by (try apply H10; smt).
    smt. 
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres_ev => //;exists i{2}; progress; apply H7.

    apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h.
    elim (H5 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq {hl}.
    cut hneq:  j <> i{2}; first by apply not_def => heq'; 
      generalize H12 hstarted; rewrite heq'.
    generalize heq; 
    elim /tuple3_ind (proj AKE_Enforcement.mStarted{1}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_Enforcement.mEexp{1}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{2}; exists j; do !split => //.
    apply H7.
    cut: (proj AKE_Enforcement.mEexp{1}.[i{2}]) =
         (proj AKE_Enforcement.mEexp{1}.[j]); first by apply gen_epk_inj.
    cut h':= H7 i{2} => h''.
    apply proj_inj_some.
     by generalize h'; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.

   by apply no_accept_coll_pres => //; smt. 
   by apply valid_accept_pres => //; smt.
   by apply inv_started_pres_ev => //; apply H7 => //.
   apply inv_accepted_pres_ev2 => //.
    by apply not_def => h; cut: in_dom i{2} AKE_Enforcement.mStarted{1} by apply H9.
    by smt.

   by apply H7 => //.
   by smt.
   by rewrite in_dom_set; left; apply H9.
   generalize H15; rewrite in_dom_set => [|] hor; last by rewrite hor  get_setE; smt.
   rewrite get_setNE.
    by apply not_def => heq; generalize heq hor H13 => ->.
    by apply H10.
   
   fun; sp; if => //; wp; skip; progress => //.
   by smt.
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
   apply H7 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_Enforcement.mStarted{1}.[i{2}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 

   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Enforcement.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Enforcement.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Enforcement.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{2}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Enforcement.mStarted{1}.[i{2}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H5 (A', B', gen_epk (proj AKE_Enforcement.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq; progress => //.
    by apply H7.
    by cut:= H10 i{2} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H7.
  by apply H7.
  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H14; rewrite in_dom_setNE // => h; apply H9.
   case (x = i{2}).
    by intros => ->; cut:= H10 i{2} _ _.
    by intros => hneq; apply H10 => //; generalize H15; rewrite in_dom_set; smt.

  by apply H7.
  by apply H9.
  by apply H10.

   fun; sp; if => //; wp; skip; progress => //.
   by smt.
 
   apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{2}; split; smt.
   
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt.
  
   apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Enforcement.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Enforcement.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{2}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.
  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H5 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{2}) => heq'.
     by generalize heq' H13 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H16 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H16 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{2}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H5 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by apply H7.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H16 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H16 /=.

   apply inv_accepted_pres_ev2.
   

call 
(_ :
  (!fresh (proj AKE_NoColl.test) AKE_NoColl.evs),
  (AKE_NoColl.evs{2} = AKE_Enforcement.evs{1} /\
  AKE_NoColl.test{2} = AKE_Enforcement.test{1} /\
  AKE_NoColl.cSession{2} = AKE_Enforcement.cSession{1} /\
  AKE_NoColl.cH2{2} = AKE_Enforcement.cH2{1} /\
  AKE_NoColl.mH2{2} = AKE_Enforcement.mH2{1} /\
  AKE_NoColl.sH2{2} = AKE_Enforcement.sH2{1} /\
  AKE_NoColl.mSk{2} = AKE_Enforcement.mSk{1} /\
  AKE_NoColl.mEexp{2} = AKE_Enforcement.mEexp{1} /\
  AKE_NoColl.mStarted{2} = AKE_Enforcement.mStarted{1} /\
  AKE_NoColl.mCompleted{2} = AKE_Enforcement.mCompleted{1} /\

  AKE_Enforcement.test{1} <> None),
  AKE_Enforcement.test{1} <> None) => //.

  by apply A_Lossless.
  (* relational spec for eexpRev *)
  fun.
  seq 1 1: 
( ! ! fresh (proj AKE_EexpRev.test{2}) AKE_EexpRev.evs{2} /\
  ={i, a, r} /\
  AKE_EexpRev.evs{2} = AKE_Enforcement.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Enforcement.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Enforcement.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Enforcement.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Enforcement.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Enforcement.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Enforcement.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Enforcement.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Enforcement.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Enforcement.mCompleted{1} /\
  ! AKE_Enforcement.test{1} = None);first by wp.
  if{1}.
  by rcondt{2} 1 => //; wp; skip; progress; smt.
  if{2} => //.
  conseq (_ : _ ==>  ! AKE_Enforcement.test{1} = None /\ 
                     ! fresh (proj AKE_EexpRev.test{2}) AKE_EexpRev.evs{2});first smt.
  by wp; skip; progress => //;smt.

  (* valid test preservation for eeexpreveal *)
  by intros &2 hunfresh; fun; wp; skip; progress.
  (* not fresh preservation for eeexpreveal *)
  intros &1; fun; wp; skip; progress try smt.
  generalize H.
  rewrite !fresh_eq_notfresh.
  cut h := 
   notfresh_fresh (proj AKE_EexpRev.test{hr}) AKE_EexpRev.evs{hr} (EphemeralRev
     (compute_psid AKE_EexpRev.mStarted{hr} AKE_EexpRev.mEexp{hr} i{hr})); smt. 
  (* relational spec for h2 *)
  fun;sp; if => //;inline AKE_Enforcement(A).O.h2  AKE_EexpRev(A).O.h2; wp; rnd; wp.
  by skip; progress => //; smt.
  (* valid test preservation for h2 *)
  intros &2 hunfresh; fun.
  inline AKE_Enforcement(A).O.h2; sp; if => //;wp; rnd => //;
      first (by apply TKey.Dword.lossless).
  by wp; skip; progress.
  (* not fresh preservation for h2 *)
  intros &1; fun.
  inline AKE_EexpRev(A).O.h2; sp; if => //;wp; rnd => //;
      first (by apply TKey.Dword.lossless).
  by wp; skip; progress => //.
  (* relational spec for Init1 *)
  by fun; wp; skip; smt.
  (* valid test preservation for Init1 *)
  intros => &2 hfresh; fun; wp; skip; smt.
  


(* end proof: }*) 