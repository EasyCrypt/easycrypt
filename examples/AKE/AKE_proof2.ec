require import Option.
require import List.
require import Map.
require import FSet.
require import Int.
require import AKE_defs.
require import Real.

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
  fun choose(s : Pk list) : Sidx {* O.eexpRev O.init1 O.init2 O.resp O.staticRev
                                    O.h2_a O.sessionRev }
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
      i = i + 1;
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


lemma collision_eexp_rcvd_mon :
forall e evs,
 collision_eexp_rcvd evs =>
 collision_eexp_rcvd (e::evs).
proof strict.
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
proof strict.
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

lemma nosmt fresh_eq_notfresh(t : Sid) (evs : Event list) :
  (! fresh t evs) =
  (notfresh t evs).
proof strict.
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
proof strict.
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

lemma coll_or_not_fresh_mon : forall e s evs,
 e <> Accept (cmatching s) =>
 e <> Start (psid_of_sid (cmatching s)) =>
(!fresh s evs \/ collision_eexp_rcvd evs ) =>
(!fresh s (e::evs) \/ collision_eexp_rcvd(e::evs)).
proof strict.
 intros => e s evs hneq1 hneq2 [|] hor; last first.
 by right; apply collision_eexp_rcvd_mon.
 
 left; generalize hor.
 rewrite !fresh_eq_notfresh => hnfr.
 apply notfresh_fresh => //.
save.

lemma coll_or_not_fresh_mon_ev : 
forall e evs s,
List.mem (Accept s) evs =>
no_start_coll(e::evs) =>
no_accept_coll(e::evs) =>
valid_accepts (e::evs) =>
(!fresh s evs \/ collision_eexp_rcvd evs ) =>
(!fresh s (e::evs) \/ collision_eexp_rcvd(e::evs)).
proof strict.
 intros => e evs s hacc hnsc hnac hvalid hor.
 case (collision_eexp_rcvd (e :: evs)) => // hncoll.
 elim hor => {hor} hor.
 left; apply coll_fresh => //.
 cut: collision_eexp_rcvd (e :: evs); last by smt.
 by apply collision_eexp_rcvd_mon.
save.

pred test_fresh(t : Sid option, evs : Event list) =
  t <> None /\ fresh (proj t) evs.

op fresh_op : Sid -> Event list-> bool.

axiom fresh_op_def : forall s evs,
fresh s evs <=> fresh_op s evs = true.

lemma fresh_op_def' : forall s evs,
fresh s evs = (fresh_op s evs = true) by smt.

lemma coll_or_not_fresh_test_mon_ev :
forall e evs s,
List.mem (Accept (proj s)) evs =>
no_start_coll(e::evs) =>
no_accept_coll(e::evs) =>
valid_accepts (e::evs) =>
(!test_fresh s evs \/ collision_eexp_rcvd evs ) =>
(!test_fresh s (e::evs) \/ collision_eexp_rcvd(e::evs)).
proof strict.
 intros => e evs s hmem hsc hnac hv.
case (s = None).
 rewrite /test_fresh => ->; by smt.
 intros => hn.
 cut heq: forall e, test_fresh s e = fresh (proj s) e.
 rewrite /test_fresh; smt.
 rewrite !heq => _.
 by apply coll_or_not_fresh_mon_ev.
save.

axiom gen_epk_inj : forall e1 e2,
gen_epk e1 = gen_epk e2 =>
e1 = e2.

axiom gen_pk_inj : forall s1 s2, 
gen_pk s1 = gen_pk s2 =>
s1 = s2.

(* simulation between traces used in last step *)
op tr_sim  : Event list -> Event list -> bool.

axiom tr_sim_empty : tr_sim [] [].
axiom tr_sim_eq_ev : forall (e : Event)(tr1 tr2 : Event list), tr_sim tr1 tr2 => tr_sim (e::tr1) (e::tr2).
axiom tr_sim_skip_sRev : forall (s : Sid)(tr1 tr2 : Event list), tr_sim tr1 tr2 => 
                                                                 tr_sim ((SessionRev s)::tr1) tr2.
axiom tr_sim_dup_sRev :  forall s tr1 tr2, tr_sim tr1 tr2 =>
                                           mem (SessionRev s) tr1 => 
                                           tr_sim tr1 ((SessionRev s)::tr2).


axiom tr_sim_inversion :
forall tr1 tr2, tr_sim tr1 tr2 => 
  ((tr1 = [] /\ tr2 = []) \/
   (exists tr1', exists tr2', exists e, tr1 = e :: tr1' /\ tr2 = e :: tr2' /\ tr_sim tr1' tr2') \/
   (exists tr1', exists s, tr1 = (SessionRev s) :: tr1' /\ tr_sim tr1' tr2) \/
   (exists tr2', exists s, tr2 = (SessionRev s) :: tr2' /\ tr_sim tr1 tr2' /\ mem (SessionRev s) tr1)).

require import Fun.

axiom tr_sim_ind (P : (Event list * Event list) cpred) :
P ([], []) =>
(forall e tr1 tr2, P (tr1, tr2) => P (e::tr1, e::tr2)) =>
(forall s tr1 tr2, P (tr1, tr2) => P ((SessionRev s) :: tr1, tr2)) =>
(forall s tr1 tr2, P (tr1, tr2) => mem (SessionRev s) tr1 => P (tr1, (SessionRev s) :: tr2)) => 
forall tr1 tr2, tr_sim tr1 tr2 => P (tr1, tr2).


(* membership preservation properties *)
lemma tr_sim_mem : forall tr1 tr2,
tr_sim tr1 tr2 => forall e, (forall s, e <> SessionRev s) => mem e tr1 = mem e tr2.
proof strict.
 intros => tr1 tr2 h.
 pose p := lambda p, let (tr1, tr2) = p in
           forall (e : Event),  (forall (s : Sid), ! e = SessionRev s) => List.mem e tr1 = List.mem e tr2.
 cut : p (tr1, tr2); last first.
 by rewrite /p /=.
 apply tr_sim_ind; rewrite /p //=.
  by progress; rewrite !mem_cons H //.
  by progress; rewrite mem_cons; (case (e = SessionRev s) => //=; first smt); rewrite H.
  by progress; rewrite mem_cons; (case (e = SessionRev s) => //=; first smt); rewrite H.
save.


lemma tr_sim_mem_sRev : forall tr1 tr2,
tr_sim tr1 tr2 => forall s, mem (SessionRev s) tr2 => mem (SessionRev s) tr1.
proof strict.
 intros => tr1 tr2 h.
 pose p := lambda p, let (tr1, tr2) = p in
         forall (s : Sid),  List.mem (SessionRev s) tr2 => List.mem (SessionRev s) tr1.
 cut : p (tr1, tr2); last first.
 by rewrite /p /=.
 apply tr_sim_ind; rewrite /p //=.
  by progress; generalize H0; rewrite !mem_cons =>[ -> |h'];[left| rewrite H].
  by progress; rewrite mem_cons H //; right.
  by progress => //; generalize H1; rewrite !mem_cons => [ -> // | h']; apply H.
save.

(* preservation of freshness *)
lemma tr_sim_fresh : forall tr1 tr2,
tr_sim tr1 tr2 => forall ts, fresh ts tr1 => fresh ts tr2.
proof strict.
 intros => tr1 tr2 hsim ts.
 elim /tuple5_ind ts => A B X Y r ?.
 rewrite /fresh /=.
 progress.
  by apply not_def => hmem; generalize H0 => /=; apply (tr_sim_mem_sRev _ tr2).
  by generalize H1; rewrite !not_and => [|] h; [left | right];rewrite -(tr_sim_mem tr1) //; smt.
  by apply not_def => hmem; generalize H2 => /=; apply (tr_sim_mem_sRev _ tr2).
  cut h := H3 _.
  by rewrite (tr_sim_mem tr1 tr2) //; first smt.
  elim h => {h} [h1 h2].
  elim h1 => {h1} h1.
   by left; rewrite -(tr_sim_mem tr1 tr2) //; first smt.
   elim h1 => {h1} h11 h12; right.
   split; first by rewrite -(tr_sim_mem tr1 tr2) //; first smt.
   apply not_def => [[z]] hz; generalize h12 => /=.
    exists z; rewrite (tr_sim_mem tr1 tr2) => //; first smt.
  cut h := H3 _.
  by rewrite (tr_sim_mem tr1 tr2) //; first smt.
  elim h => ?.
  rewrite (tr_sim_mem tr1 tr2) //; first smt.
save.

lemma tr_sim_fresh_op : forall tr1 tr2,
tr_sim tr1 tr2 => forall ts, fresh_op ts tr1 => fresh_op ts tr2.
proof strict.
intros => tr1 tr2 hsim ts.
cut: fresh_op ts tr1 = true => fresh_op ts tr2 = true; last by smt.
rewrite -!fresh_op_def'.
by apply tr_sim_fresh.
save.


section.
declare module A : Adv2{ AKE_EexpRev, AKE_eqS}.

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

local module AKE_Fresh(FA : Adv2) = {
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
      ((test <> None) => 
      fresh_op (proj test) (EphemeralRev(compute_psid mStarted mEexp i)::evs ))) {
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
      if ( in_dom A mSk && in_dom B mSk && !in_dom i mStarted ) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
       (test <> None => 
       fresh_op (proj test) 
        (Accept(compute_sid mStarted mEexp mCompleted.[i<- Y] i)::evs ))) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk &&
      ((test <> None => 
       fresh_op (proj test) (StaticRev A::evs )))) {
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
     ((test <> None) =>
      fresh_op (proj test) (SessionRev
          (compute_sid mStarted mEexp mCompleted i)::evs) )) {
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
      i = i + 1;
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
      if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None &&
          fresh_op (compute_sid mStarted mEexp mCompleted t_idx) evs) {
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

(* useful lemmas for the invariants *)

lemma no_start_coll_pres : 
forall e evs, 
 (forall s, e <> Start s) =>
 no_start_coll evs =>
 no_start_coll (e :: evs).
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
 intros => m; rewrite /start_evs_eexps; smt.
save.

lemma start_evs_eexps_pres :
forall e evs m,
start_evs_eexps evs m =>
(forall s, e <> Start s) =>
start_evs_eexps (e::evs) m.
proof strict.
 intros e evs m; rewrite /start_evs_eexps  => htl hneq s; rewrite mem_cons => [|] hor.
 by cut _ := hneq s; smt.
 by apply htl.
save.

lemma start_evs_eexps_pres_ev :
forall evs m s,
start_evs_eexps evs m =>
(exists e, in_dom e m /\ psid_sent s = gen_epk (proj (m.[e]))) =>
start_evs_eexps (Start s::evs) m.
proof strict.
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
proof strict.
 intros => m; rewrite /accept_evs_eexps; smt.
save.


lemma accept_evs_eexps_pres :
forall e evs m,
accept_evs_eexps evs m =>
(forall s, e <> Accept s) =>
accept_evs_eexps (e::evs) m.
proof strict.
 intros e evs m; rewrite /accept_evs_eexps  => htl hneq s; rewrite mem_cons => [|] hor.
 by cut _ := hneq s; smt.
 by apply htl.
save.

lemma accept_evs_eexps_pres_ev :
forall evs m s,
accept_evs_eexps evs m =>
(exists e, in_dom e m /\ sid_sent s = gen_epk (proj (m.[e]))) =>
accept_evs_eexps (Accept s::evs) m.
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
 intros => evs e m1 m2; rewrite /inv_started => htl hnstsrt ps; 
  rewrite mem_cons; split.
   intros => [|] h.
    by cut:= hnstsrt ps; smt. 
    by cut [h1 hcl]:= htl ps => {hcl};apply h1.
 
   intros => [i][hdom1][hdom2] heq.
   cut [h1 hcl]:= htl ps => {h1}; right; apply hcl.
   exists i; progress => //.
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
proof strict.
  intros => evs A0 B m1 m2 i; rewrite /inv_started => hinv hindom hnindom ps;
   rewrite mem_cons; split.
   intros => [heq|hmem].
   cut: ps = (A0, B, gen_epk (proj m2.[i]), init); first by apply Start_inj.
   intros => {heq} heq.
   exists i; progress => //.
    by rewrite in_dom_setE.
    by generalize H; rewrite get_setE proj_some.
    by generalize H; rewrite get_setE proj_some.
 
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
proof strict.
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
proof strict.
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
proof strict.
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
proof strict.
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

lemma proj_inj_some : 
forall (x y : 'a option),
x <> None => 
y <> None =>
proj x = proj y =>
x = y.
proof strict.
 intros => x y;elim /option_case_eq x => //;elim /option_case_eq y => //.
 by intros=> [x'] -> [y'] ->; rewrite !proj_some.
save.


local equiv eq1_choose : 
AKE_Fresh(A).A.choose ~ AKE_EexpRev(A).A.choose : 
 ={s, glob A} /\
 (AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  AKE_Fresh.test{1} = None /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll(AKE_EexpRev.evs{2}) /\
  no_accept_coll(AKE_EexpRev.evs{2}) /\
  valid_accepts (AKE_EexpRev.evs{2}) /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2}  /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} 
             AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\ 
  (forall x, in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall x, in_dom x AKE_EexpRev.mStarted{2} => !in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj (AKE_EexpRev.mStarted{2}.[x])) = init)) ==>
 ={res, glob A} /\
 (AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  AKE_Fresh.test{1} = None /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll(AKE_EexpRev.evs{2}) /\
  no_accept_coll(AKE_EexpRev.evs{2}) /\
  valid_accepts (AKE_EexpRev.evs{2}) /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2}  /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} 
             AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\ 
  (forall x, in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall x, in_dom x AKE_EexpRev.mStarted{2} => !in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj (AKE_EexpRev.mStarted{2}.[x])) = init)).
proof strict.
 fun (AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  AKE_Fresh.test{1} = None /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll(AKE_EexpRev.evs{2}) /\
  no_accept_coll(AKE_EexpRev.evs{2}) /\
  valid_accepts (AKE_EexpRev.evs{2}) /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2}  /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} 
             AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\ 
  (forall x, in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall x, in_dom x AKE_EexpRev.mStarted{2} => !in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj (AKE_EexpRev.mStarted{2}.[x])) = init)).
progress => //; try apply H9; smt.
progress => //; try apply H9; smt.

fun; wp; skip; progress => //.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.  

    fun; sp; (if; first smt);
    inline AKE_Fresh(A).O.h2  AKE_EexpRev(A).O.h2;
    wp; try rnd; wp; skip; progress.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres_ev => //;exists i{2}; progress => //; smt.

    apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h.
    elim (H4 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq {hl}.
    cut hneq:  j <> i{2}; first by apply not_def => heq'; 
      generalize H12 hstarted; rewrite heq'.
    generalize heq; 
    elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{2}; exists j; do !split => //.
    by apply H6.
    cut: (proj AKE_Fresh.mEexp{1}.[i{2}]) =
         (proj AKE_Fresh.mEexp{1}.[j]); first by apply gen_epk_inj.
    cut h':= H6 i{2} => h''.
    apply proj_inj_some.
     by generalize h'; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.

   by apply no_accept_coll_pres => //; smt. 
   by apply valid_accept_pres => //; smt.
   by apply inv_started_pres_ev => //; apply H6 => //.
   apply inv_accepted_pres_ev2 => //.
    by apply not_def => h; cut: in_dom i{2} AKE_Fresh.mStarted{1} by apply H8.
    by smt.

   by rewrite in_dom_set; left; apply H8.
   generalize H13; rewrite in_dom_set => [|] hor; last by rewrite hor  get_setE; smt.
   rewrite get_setNE.
    by apply not_def => heq; generalize heq hor H12 => ->.
    by apply H9.

   fun; sp; if => //; wp; skip; progress => //.
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
    by apply H6 => //.
    
    rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
    by elim /tuple3_ind  (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=.
  
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 

   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H5 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H6.
      apply proj_inj_some.
       by cut:= H6 i{2}; rewrite /in_dom.
       by cut:= H6 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H4 (A', B', gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq; progress => //.
    by apply H6.
    by cut:= H9 i{2} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
   by apply H6.
  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H12; rewrite in_dom_setNE // => h; apply H8.
   case (x = i{2}).
    by intros => ->; cut:= H9 i{2} _ _.
    by intros => hneq; apply H9 => //; generalize H13; rewrite in_dom_set; smt.

   fun; sp; if => //; wp; skip; progress => //.

   apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{2}; split; smt.
   
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt.
  
   apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H5 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H9; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H6.
      apply proj_inj_some.
       by cut:= H6 i{2}; rewrite /in_dom.
       by cut:= H6 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.
  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H4 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{2}) => heq'.
     by generalize heq' H12 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H14 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H14 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{2}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H4 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H14 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H14 /=.

   rewrite /inv_accepted => ps; rewrite mem_cons; split.
    intros => [|] hor.
    cut: ps = (B{2}, A{2}, gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), X{2}, resp).
     by apply Accept_inj.
    intros => ->.
   exists i{2}; rewrite !in_dom_setE /compute_sid !get_setE !proj_some /=.
    by apply H6.
 
   cut [h1 h2] := H5 ps => {h2}.
   cut:= h1 _ => //; intros => [j][hdom1][hdom2][hdom3] heq.
    case (j = i{2}) => heq'.
     by generalize heq' H12 hdom1 => ->; smt.
     exists j; (rewrite !in_dom_setNE // /compute_sid heq !get_setNE; first 2 smt).
     by do !split => //.
   intros => [j][hdom1][hdom2][hdom3] heq.
   case (i{2} = j) => hor.
    generalize heq; rewrite hor.
    by rewrite /compute_sid /= !get_setE !proj_some /= => ->; left.  
   
   right.
   cut [h1 h2]:= H5 ps => {h1}.
   apply h2.
   exists j.
   generalize hdom1 hdom2 hdom3 heq; 
   rewrite !in_dom_setNE; first 2 smt. 
   by rewrite /compute_sid /= !get_setNE /=; smt.
   generalize H14; rewrite !in_dom_set => [|] hor.
    by left; apply H8.
    by right.
   case (x = i{2}) => hor.
    by generalize hor H15 => ->; rewrite in_dom_setE.
    rewrite get_setNE; first smt.
    apply H9.
    by generalize H14; rewrite !in_dom_setNE.
    by generalize H15; rewrite !in_dom_setNE. 
       
   fun; wp; skip; progress; try assumption.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  

   fun; sp; if => //.
    inline  AKE_Fresh(A).O.h2 AKE_EexpRev(A).O.h2; wp; rnd; wp; skip; progress.

    fun.
    sp; if; first smt.
    inline  AKE_Fresh(A).O.computeKey AKE_EexpRev(A).O.computeKey.
    sp; if; first smt.
    inline  AKE_Fresh(A).O.h2 AKE_EexpRev(A).O.h2.
    wp; rnd; wp; skip; progress; try assumption.
     by apply accept_evs_eexps_pres => //; smt.
     by apply start_evs_eexps_pres => //; smt.
     by apply no_start_coll_pres => //; smt. 
     by apply no_accept_coll_pres => //; smt. 
     by apply valid_accept_pres => //; smt. 
     by apply inv_started_pres => //; smt.  
     by apply inv_accepted_pres => //; smt.  
     by apply accept_evs_eexps_pres => //; smt.
     by apply start_evs_eexps_pres => //; smt.
     by apply no_start_coll_pres => //; smt. 
     by apply no_accept_coll_pres => //; smt. 
     by apply valid_accept_pres => //; smt. 
     by apply inv_started_pres => //; smt.  
     by apply inv_accepted_pres => //; smt.  

    wp; skip; smt.
    wp; skip; progress.
save.


local equiv eq1_eexpRev :
AKE_Fresh(A).O.eexpRev ~ AKE_EexpRev(A).O.eexpRev :
 ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i, a} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>
if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun.
seq 1 1:
( ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i, a} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} /\ 
  ={r} /\ r{2} = None).
wp; skip; progress => //.
if{1}.
rcondt{2} 1.
intros &m; skip; smt.
wp; skip; progress => //.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt.
    by apply no_accept_coll_pres => //; smt.
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt.
    by apply no_accept_coll_pres => //; smt.
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.
    by rewrite mem_cons; right.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt.
    by apply no_accept_coll_pres => //; smt.
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt.
    by apply no_accept_coll_pres => //; smt.
    by apply valid_accept_pres => //; smt.
    by apply inv_started_pres => //; smt.
    by apply inv_accepted_pres => //; smt.
    by rewrite mem_cons; right.
    if{2}.
    conseq (_ :_ ==>
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init ) /\
     AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}).
     progress => //; try (apply H12); try smt.

     wp; skip; progress => //.

      by rewrite /test_fresh; smt.
      by apply accept_evs_eexps_pres => //; smt.
      by apply start_evs_eexps_pres => //; smt.
      by apply no_start_coll_pres => //; smt.
      by apply no_accept_coll_pres => //; smt.
      by apply valid_accept_pres => //; smt.
      by apply inv_started_pres => //; smt.
      by apply inv_accepted_pres => //; smt.
      by rewrite mem_cons; right.
     skip; smt.
save.

local lemma  bdh1_eexpRev1 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.eexpRev :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 by intros => &2 h; fun; wp; skip; progress; rewrite mem_cons; right.
save.


local lemma bdh1_eexpRev2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.eexpRev :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros &1; fun; wp; skip; progress => //.
  case (AKE_EexpRev.test{hr} = None); first smt.
  intros => h.
  generalize H.
  cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  rewrite !heq //.
  by intros => h'; apply coll_or_not_fresh_mon => //; smt.

  by apply accept_evs_eexps_pres; smt.
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.
  by apply inv_accepted_pres => //; smt.
  by rewrite mem_cons; right.
save.


local equiv eq1_h2 :
    AKE_Fresh(A).O.h2 ~ AKE_EexpRev(A).O.h2 :
! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={sstring} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>

 if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun; wp; rnd; skip; smt. 
save.

local equiv eq1_h2_a :
    AKE_Fresh(A).O.h2_a ~ AKE_EexpRev(A).O.h2_a :
! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={sstring} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>

 if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
fun.
sp; if; first smt.
 wp; call eq1_h2; wp; skip; progress => //.
  by elim H30; smt.
  by elim H30; smt.
  by skip; progress => //.
save.

local lemma  bdh1_h2_a_1 : 
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.h2_a :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros &2 h.
 fun.
 sp; if.
  inline AKE_Fresh(A).O.h2; wp; rnd; wp; skip; progress => //.
   by apply TKey.Dword.lossless.

  skip; progress => //. 
save. 

local lemma bdh1_h2_a_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.h2_a :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros => &1.
 fun.
 sp; if.
  inline AKE_EexpRev(A).O.h2;wp; rnd; wp; skip; progress => //.
   by apply TKey.Dword.lossless.

  skip; progress => //. 
save.


local equiv eq1_init1 :
   AKE_Fresh(A).O.init1 ~ AKE_EexpRev(A).O.init1 : 
! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i, A, B} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>
if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun; wp; skip; progress => //.
  by apply accept_evs_eexps_pres; smt.
  by apply start_evs_eexps_pres_ev => //; smt.
  apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h. 
    elim (H7 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq {hl}.
    cut hneq:  j <> i{2}; first by apply not_def => heq'; 
      generalize H12 hstarted; rewrite heq'.
    generalize heq; 
    elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{2}; exists j; do !split => //.
    apply H9.
    cut: (proj AKE_Fresh.mEexp{1}.[i{2}]) =
         (proj AKE_Fresh.mEexp{1}.[j]); first by apply gen_epk_inj.
    cut h':= H9 i{2} => h''.
    apply proj_inj_some.
     by generalize h'; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres_ev => //; apply H9 => //.
  apply inv_accepted_pres_ev2 => //.
   by apply not_def => h; cut: in_dom i{2} AKE_Fresh.mStarted{1} by apply H11.
   by smt.
   by rewrite in_dom_set; left; apply H11.
   by rewrite mem_cons; right; assumption.
   generalize H18; rewrite in_dom_set => [|] hor; last by rewrite hor  get_setE; smt.
   rewrite get_setNE.
    by apply not_def => heq; generalize heq hor H16 => ->.
    by apply H12.
   by rewrite mem_cons; right; assumption.
   by rewrite mem_cons; right; assumption.
  by apply accept_evs_eexps_pres; smt. 
  by apply start_evs_eexps_pres_ev => //; smt.
  apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h.
    elim (H7 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq {hl}.
    cut hneq:  j <> i{2}; first by apply not_def => heq'; 
      generalize H12 hstarted; rewrite heq'.
    generalize heq; 
    elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{2}; exists j; do !split => //.
    apply H9.
    cut: (proj AKE_Fresh.mEexp{1}.[i{2}]) =
         (proj AKE_Fresh.mEexp{1}.[j]); first by apply gen_epk_inj.
    cut h':= H9 i{2} => h''.
    apply proj_inj_some.
     by generalize h'; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.
  by apply no_accept_coll_pres => //; smt. 
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres_ev => //; apply H9 => //.
  apply inv_accepted_pres_ev2 => //.
   by apply not_def => h; cut: in_dom i{2} AKE_Fresh.mStarted{1} by apply H11.
   by smt.
   by rewrite in_dom_set; left; apply H11.
   generalize H18; rewrite in_dom_set => [|] hor; last by rewrite hor  get_setE; smt.
   rewrite get_setNE.
    by apply not_def => heq; generalize heq hor H16 => ->.
    by apply H12.
by rewrite mem_cons; right.
save.


local lemma bdh1_init11 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.init1 :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros => &2 h; fun; wp; skip; progress => //; rewrite ?mem_cons; try (apply H11 ); smt.
save.

local lemma bdh1_init1_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.init1 :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
intros &1; fun; wp; skip; progress => //.
elim H => h; last first.
by right; apply collision_eexp_rcvd_mon.
  cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq //.
  intros => h.
  case (collision_eexp_rcvd
  (Start (A{hr}, B{hr}, gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), init) :: AKE_EexpRev.evs{hr})) => hcoll; first by right.
  left.
  apply coll_fresh => //.
  apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h'.
    elim (H5 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq' {hl}.
    cut hneq:  j <> i{hr}; first by apply not_def => heq''; 
      generalize H12 hstarted; rewrite heq''.
    generalize heq'; 
    elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h'; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{hr}; exists j; do !split => //.
    apply H7.
    cut: (proj AKE_EexpRev.mEexp{hr}.[i{hr}]) =
         (proj AKE_EexpRev.mEexp{hr}.[j]); first by apply gen_epk_inj.
    cut h':= H7 i{hr} => h''.
    apply proj_inj_some.
     by generalize h''; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.

  by apply accept_evs_eexps_pres; smt. 
  apply start_evs_eexps_pres_ev => //; exists i{hr}; progress; smt.

  apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h'.
    elim (H5 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq' {hl}.
    cut hneq:  j <> i{hr}; first by apply not_def => heq''; 
      generalize H12 hstarted; rewrite heq''.
    generalize heq'; 
    elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h'; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{hr}; exists j; do !split => //.
    apply H7.
    cut: (proj AKE_EexpRev.mEexp{hr}.[i{hr}]) =
         (proj AKE_EexpRev.mEexp{hr}.[j]); first by apply gen_epk_inj.
    cut h':= H7 i{hr} => h''.
    apply proj_inj_some.
     by generalize h''; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.

  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.

  by apply inv_started_pres_ev => //; apply H7 => //.
  apply inv_accepted_pres_ev2 => //.
  apply not_def => h; cut: in_dom i{hr} AKE_EexpRev.mStarted{hr}. 
   by apply H9.
   by smt.
   by smt.
   by rewrite in_dom_set; left; apply H9.
   generalize H17; rewrite in_dom_set => [|] hor; last by rewrite hor  get_setE; smt.
   rewrite get_setNE.
    by apply not_def => heq; generalize heq hor H16 => ->.
    by apply H12.
   by rewrite mem_cons; right; assumption.
save.

local equiv eq1_init2 : 
    AKE_Fresh(A).O.init2 ~ AKE_EexpRev(A).O.init2 :
 ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i, Y} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun.
if{1}.
   rcondt{2} 1;trivial.
   wp; skip; progress => //.
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
   apply H9 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 

   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H7 (A', B', gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq; progress => //.
    by apply H9.
    by cut:= H12 i{2} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H9.
  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H18; rewrite in_dom_setNE // => h; apply H11.
  by rewrite mem_cons; right.
   case (x = i{2}).
    by intros => ->; cut:= H12 i{2} _ _.
    by intros => hneq; apply H12 => //; generalize H19; rewrite in_dom_set; smt.

  by rewrite mem_cons; right.
  by rewrite mem_cons; right.
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
   apply H9 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 

   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H7 (A', B', gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq; progress => //.
    by apply H9.
    by cut:= H12 i{2} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H9.
  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H18; rewrite in_dom_setNE // => h; apply H11.
  case (x = i{2}).
   by intros => ->; cut:= H12 i{2} _ _.
    by intros => hneq; apply H12 => //; generalize H19; rewrite in_dom_set; smt.

  by rewrite mem_cons; right.
if{2}; last first.
 skip; progress => //.
 conseq (_ : 
((! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
       collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
    ={i, Y} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}) /\
   ! (! in_dom i{1} AKE_Fresh.mCompleted{1} &&
      in_dom i{1} AKE_Fresh.mStarted{1} &&
      (! AKE_Fresh.test{1} = None =>
       fresh_op (proj AKE_Fresh.test{1})
         (Accept
            (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
               AKE_Fresh.mCompleted{1}.[i{1} <- Y{1}] i{1}) :: AKE_Fresh.evs{1})))) /\
  ! in_dom i{2} AKE_EexpRev.mCompleted{2} &&
  in_dom i{2} AKE_EexpRev.mStarted{2} /\
(! test_fresh AKE_EexpRev.test{2}
         (Accept
            (compute_sid AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2}
               AKE_EexpRev.mCompleted{2}.[i{2} <- Y{2}] i{2}) :: AKE_EexpRev.evs{2})) ==> _).
progress => //.
rewrite /test_fresh; rewrite not_and; right; smt.
 wp; skip; progress => //; try (by apply H12); try (by apply H9);
try (by apply H11).
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
   apply H9 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 

  apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq';apply not_def => h'.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq''.
   generalize  heq'' h' => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq''.
   case (i{2} = j) => hor.
     by generalize hjstrt H15; rewrite hor; smt.

     apply not_def => heq'''. 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.


   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /= A' B' r' heq'.
   cut [h1 h2]:=
    H7 (A', B', gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq'; progress => //.
    by apply H9.
    by cut:= H12 i{2} _ _ => //; rewrite heq' /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H9.

  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H19; rewrite in_dom_setNE // => h; apply H11.
  case (x = i{2}).
   by intros => ->; cut:= H12 i{2} _ _.
   by intros => hneq; apply H12 => //; generalize H20; rewrite in_dom_set; smt.

  by rewrite mem_cons; right.
  smt.
  smt.
       
   apply accept_evs_eexps_pres_ev => //.
   exists i{2}; do !split => //.
   apply H9 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  ( proj AKE_Fresh.mStarted{1}.[i{2}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 
   
   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind ( proj AKE_Fresh.mStarted{1}.[i{2}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H12; rewrite hor; smt.

     apply not_def => heq''.
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[i{2}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H7 (A', B', gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), r') => {h1}.
   apply h2.
   exists i{2}; rewrite heq; progress => //.
    by apply H9.
    by cut:= H12 i{2} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H9.
  case (x = i{2}).
   by intros ->.
   by intros neq; generalize H19; rewrite in_dom_setNE // => h; apply H11.
  case (x = i{2}).
   by intros => ->; cut:= H12 i{2} _ _.
    by intros => hneq; apply H12 => //; generalize H20; rewrite in_dom_set; smt.

  by rewrite mem_cons; right.
save.  


local lemma bdh1_init2_1 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.init2 :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros => &2 hbad; fun; wp; skip; progress => //.
 by rewrite mem_cons; right.
save.

local lemma bdh1_init2_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.init2 :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros => &1; fun; wp; skip; progress => //.
 elim H => h; last first.
 by right; apply collision_eexp_rcvd_mon.
  cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq //.
  intros => h.
  case (collision_eexp_rcvd
  (Accept (compute_sid AKE_EexpRev.mStarted{hr} AKE_EexpRev.mEexp{hr}
        AKE_EexpRev.mCompleted{hr}.[i{hr} <- Y{hr}] i{hr}) :: AKE_EexpRev.evs{hr}))
   => hcoll; first by right.
  left.
  apply coll_fresh => //.
  by apply no_start_coll_pres => //; smt.
  apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq';apply not_def => h'.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq''.
   generalize  heq'' h' => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq''.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq'''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{hr}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /= A' B' r' heq'.
   cut [h1 h2]:=
    H5 (A', B', gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), r') => {h1}.
   apply h2.
   exists i{hr}; rewrite heq'; progress => //.
    by apply H7.
    by cut:= H12 i{hr} _ _ => //; rewrite heq' /sd2_role /=.

   apply accept_evs_eexps_pres_ev => //.
   exists i{hr}; do !split => //.
   apply H7 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /=.
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt. 

   apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq;apply not_def => h.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' h => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq'.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{hr}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
       
   apply valid_accept_pres_ev => //.   
   rewrite /psid_of_sid/compute_sid get_setE.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /= A' B' r' heq.
   cut [h1 h2]:=
    H5 (A', B', gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), r') => {h1}.
   apply h2.
   exists i{hr}; rewrite heq; progress => //.
    by apply H7.
    by cut:= H12 i{hr} _ _ => //; rewrite heq /sd2_role /=.

  by apply inv_started_pres => //; smt.   

  apply inv_accepted_pres_ev1 => //.
  by apply H7.
  case (x = i{hr}).
   by intros ->.
   by intros neq; generalize H16; rewrite in_dom_setNE // => h; apply H9.
  case (x = i{hr}).
   by intros => ->; cut:= H12 i{hr} _ _.
    by intros => hneq; apply H12 => //; generalize H17; rewrite in_dom_set; smt.

  by rewrite mem_cons; right.
save.


local equiv eq1_resp :
    AKE_Fresh(A).O.resp ~ AKE_EexpRev(A).O.resp :
  ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i, B, A, X} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==> 

 if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun; wp; skip; progress => //.
   apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{2}; split; smt.
   
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt.
  
   apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.
  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H7 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{2}) => heq'.
     by generalize heq' H15 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H19 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H19 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{2}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H7 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H19 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H19 /=.

   rewrite /inv_accepted => ps; rewrite mem_cons; split.
    intros => [|] hor.
    cut: ps = (B{2}, A{2}, gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), X{2}, resp).
     by apply Accept_inj.
    intros => ->.
   exists i{2}; rewrite !in_dom_setE /compute_sid !get_setE !proj_some /=.
    by apply H9.
 
   cut [h1 h2] := H8 ps => {h2}.
   cut:= h1 _ => //; intros => [j][hdom1][hdom2][hdom3] heq.
    case (j = i{2}) => heq'.
     by generalize heq' H15 hdom1 => ->; smt.
     exists j; (rewrite !in_dom_setNE // /compute_sid heq !get_setNE; first 2 smt).
     by do !split => //.
   intros => [j][hdom1][hdom2][hdom3] heq.
   case (i{2} = j) => hor.
    generalize heq; rewrite hor.
    by rewrite /compute_sid /= !get_setE !proj_some /= => ->; left.  
   
   right.
   cut [h1 h2]:= H8 ps => {h1}.
   apply h2.
   exists j.
   generalize hdom1 hdom2 hdom3 heq; 
   rewrite !in_dom_setNE; first 2 smt. 
   by rewrite /compute_sid /= !get_setNE /=; smt.
   generalize H19; rewrite !in_dom_set => [|] hor.
    by left; apply H11.
    by right.
   by rewrite mem_cons; right.
   case (x = i{2}) => hor.
    by generalize hor H20 => ->; rewrite in_dom_setE.
    rewrite get_setNE; first smt.
    apply H12.
    by generalize H19; rewrite !in_dom_setNE.
    by generalize H20; rewrite !in_dom_setNE. 
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.

   apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{2}; split; smt.
   
   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt.
  
   apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H8 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_Fresh.mStarted{1}.[j]) => /= A' B' r' heq'.
   case (i{2} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_Fresh.mEexp{1}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{2}; exists j; do !split => //.
      by apply H9.
      apply proj_inj_some.
       by cut:= H9 i{2}; rewrite /in_dom.
       by cut:= H9 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.
  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H7 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{2}) => heq'.
     by generalize heq' H15 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H19 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H19 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{2}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H7 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H19 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H19 /=.

   rewrite /inv_accepted => ps; rewrite mem_cons; split.
    intros => [|] hor.
    cut: ps = (B{2}, A{2}, gen_epk (proj AKE_Fresh.mEexp{1}.[i{2}]), X{2}, resp).
     by apply Accept_inj.
    intros => ->.
   exists i{2}; rewrite !in_dom_setE /compute_sid !get_setE !proj_some /=.
    by apply H9.
 
   cut [h1 h2] := H8 ps => {h2}.
   cut:= h1 _ => //; intros => [j][hdom1][hdom2][hdom3] heq.
    case (j = i{2}) => heq'.
     by generalize heq' H15 hdom1 => ->; smt.
     exists j; (rewrite !in_dom_setNE // /compute_sid heq !get_setNE; first 2 smt).
     by do !split => //.
   intros => [j][hdom1][hdom2][hdom3] heq.
   case (i{2} = j) => hor.
    generalize heq; rewrite hor.
    by rewrite /compute_sid /= !get_setE !proj_some /= => ->; left.  
   
   right.
   cut [h1 h2]:= H8 ps => {h1}.
   apply h2.
   exists j.
   generalize hdom1 hdom2 hdom3 heq; 
   rewrite !in_dom_setNE; first 2 smt. 
   by rewrite /compute_sid /= !get_setNE /=; smt.
   generalize H19; rewrite !in_dom_set => [|] hor.
    by left; apply H11.
    by right.
   case (x = i{2}) => hor.
    by generalize hor H20 => ->; rewrite in_dom_setE.
    rewrite get_setNE; first smt.
    apply H12.
    by generalize H19; rewrite !in_dom_setNE.
    by generalize H20; rewrite !in_dom_setNE. 
    by rewrite mem_cons; right.
save.

local lemma bdh1_resp_1 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.resp :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros => &2 h; fun; wp; skip; progress => //.
 by rewrite mem_cons; right.
save.


local lemma bdh1_resp_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.resp :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros => &1; fun; wp; skip; progress => //.
 elim H => h; last first.
 by right; apply collision_eexp_rcvd_mon.
  cut heq_tf :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq_tf //.
  intros => h.
  case (collision_eexp_rcvd
  (Accept(B{hr}, A{hr}, gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), X{hr}, resp) 
    :: AKE_EexpRev.evs{hr})) => hcoll; first by right.
  left.
  apply coll_fresh => //.
  by apply no_start_coll_pres => //; smt.
  apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq'.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{hr}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.

   apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{hr}; split; smt.

   by apply start_evs_eexps_pres => //; smt.
   by apply no_start_coll_pres => //; smt.

   apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H6 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq'.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H7.
      apply proj_inj_some.
       by cut:= H7 i{hr}; rewrite /in_dom.
       by cut:= H7 j; rewrite /in_dom.
       by apply gen_epk_inj.
   
   by apply valid_accept_pres_ev2.
  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H5 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{hr}) => heq'.
     by generalize heq' H15 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H18 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H18 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{hr}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H5 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H18 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H18 /=.
   rewrite /inv_accepted => ps; rewrite mem_cons; split.
    intros => [|] hor.
    cut: ps = (B{hr}, A{hr}, gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), X{hr},resp).
     by apply Accept_inj.
    intros => ->.
   exists i{hr}; rewrite !in_dom_setE /compute_sid !get_setE !proj_some /=.
    by apply H7.
 
   cut [h1 h2] := H6 ps => {h2}.
   cut:= h1 _ => //; intros => [j][hdom1][hdom2][hdom3] heq.
    case (j = i{hr}) => heq'.
     by generalize heq' H15 hdom1 => ->; smt.
     exists j; (rewrite !in_dom_setNE // /compute_sid heq !get_setNE; first 2 smt).
     by do !split => //.
   intros => [j][hdom1][hdom2][hdom3] heq.
   case (i{hr} = j) => hor.
    generalize heq; rewrite hor.
    by rewrite /compute_sid /= !get_setE !proj_some /= => ->; left.  

   right.
   cut [h1 h2]:= H6 ps => {h1}.
   apply h2.
   exists j.
   generalize hdom1 hdom2 hdom3 heq; 
   rewrite !in_dom_setNE; first 2 smt. 
   by rewrite /compute_sid /= !get_setNE /=; smt.

   generalize H18; rewrite !in_dom_set => [|] hor.
    by left; apply H9.
    by right.
   case (x = i{hr}) => hor.
    by generalize hor H19 => ->; rewrite in_dom_setE.
    rewrite get_setNE; first smt.
    apply H12.
    by generalize H18; rewrite !in_dom_setNE.
    by generalize H19; rewrite !in_dom_setNE. 
    by rewrite mem_cons; right.
save.   

local equiv eq1_staticRev : 
    AKE_Fresh(A).O.staticRev ~ AKE_EexpRev(A).O.staticRev :
  ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={A} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
fun.
seq 1 1:
( ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={A} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} /\ 
 ={r} /\ r{2} = None).
wp; skip; progress => //.
if{1}.
rcondt{2} 1.
intros => ?; wp; progress => //.
wp; skip; progress => //.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by rewrite mem_cons; right.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  
    by rewrite mem_cons; right.

   if{2}.
   conseq (_ : _ ==>
 (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\ 
 accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}).
progress => //; try (apply H12); smt.
wp; skip; progress => //.    
    cut heq' : forall p q, (p && q) = (p /\ (p => q)) by smt.
    cut heq'' : forall p q, (p => q) = (!p \/ q) by smt.
    generalize H14; rewrite heq' not_and => [|]; first by smt.
     rewrite (heq'' (in_dom A{2} AKE_Fresh.mSk{1})) not_or => [hv].
     rewrite (heq'' (! AKE_Fresh.test{1} = None)) not_or => [hv'].
   cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
   cut nnp : forall p, (! ! p) = p by smt.
   by rewrite heq // fresh_op_def'; smt.
    by apply accept_evs_eexps_pres => //; smt.
    by apply start_evs_eexps_pres => //; smt.
    by apply no_start_coll_pres => //; smt. 
    by apply no_accept_coll_pres => //; smt. 
    by apply valid_accept_pres => //; smt. 
    by apply inv_started_pres => //; smt.  
    by apply inv_accepted_pres => //; smt.  
    by rewrite mem_cons; right.

   skip; progress => //.
qed.

local lemma bdh1_staticRev_1 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.staticRev :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros => &2 h; fun; wp; skip; progress => //.
  by rewrite mem_cons; right.
save.


local lemma bdh1_staticRev_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.staticRev :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros => &1; fun; wp; skip; progress => //.
 elim H => h; last first.
 by right; apply collision_eexp_rcvd_mon.
  cut heq_tf :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq_tf //.
  intros => h.
  case (collision_eexp_rcvd (StaticRev A{hr} :: AKE_EexpRev.evs{hr})) => hcoll; 
   first by right.
  left.
  apply coll_fresh => //.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  by rewrite mem_cons; right.
qed.  


local equiv eq1_computeKey :
    AKE_Fresh(A).O.computeKey ~ AKE_EexpRev(A).O.computeKey :
  ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>
  if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun; sp; if; first by smt.
  wp.
  call eq1_h2.
  wp; skip; progress => //.
   smt.   
   smt.
  wp; skip; progress => //.
save. 
  

local equiv eq1_sessionRev :
    AKE_Fresh(A).O.sessionRev ~ AKE_EexpRev(A).O.sessionRev :
  ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\
  ={i} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
  mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
==>
  if ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2} then
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}
  else
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun; sp.
 if{1}.
 rcondt{2} 1.
 intros => ?; wp; skip; progress; smt. 
 call eq1_computeKey.
 wp; skip; progress => //.
 generalize H; rewrite !not_or => [h1 h2]; split => //.
   cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  by rewrite heq // fresh_op_def'; smt.
  by apply n_exp_recvd_coll => //; smt.
  by rewrite mem_cons; right.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  by rewrite mem_cons; right.
if{2}.
   conseq (_ : _ ==>
 (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) /\ 
 accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    ! AKE_Fresh.test{1} = None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mStarted{2} =>
       ! in_dom x AKE_EexpRev.mCompleted{2} =>
       sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
    mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}).
progress => //; try (apply H12); smt.
wp.
inline AKE_EexpRev(A).O.computeKey.
inline AKE_EexpRev(A).O.h2.
sp.
if{2}.
wp; rnd{2}; wp; skip; progress => //.
   by apply TKey.Dword.lossless.
    cut heq' : forall p q, (p && q) = (p /\ (p => q)) by smt.
    cut heq'' : forall p q, (p => q) = (!p \/ q) by smt.
    generalize H14; rewrite heq' not_and => [|]; first by smt.
     rewrite (heq'' (in_dom i{2} AKE_Fresh.mCompleted{1})) not_or => [hv].
     rewrite (heq'' (! AKE_Fresh.test{1} = None)) not_or => [hv'].
   cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
   cut nnp : forall p, (! ! p) = p by smt.
   by rewrite heq // fresh_op_def'; smt.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  by rewrite mem_cons; right.
 wp; skip; progress => //.
    cut heq' : forall p q, (p && q) = (p /\ (p => q)) by smt.
    cut heq'' : forall p q, (p => q) = (!p \/ q) by smt.
    generalize H14; rewrite heq' not_and => [|]; first by smt.
     rewrite (heq'' (in_dom i{2} AKE_Fresh.mCompleted{1})) not_or => [hv].
     rewrite (heq'' (! AKE_Fresh.test{1} = None)) not_or => [hv'].
   cut heq :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
   cut nnp : forall p, (! ! p) = p by smt.
   by rewrite heq // fresh_op_def'; smt.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt. 
  by rewrite mem_cons; right.
skip; progress => //.
save.

local lemma bdh1_sessionRev_1 :
forall &2,
  ! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
  collision_eexp_rcvd AKE_EexpRev.evs{2} =>
  bd_hoare[ AKE_Fresh(A).O.sessionRev :
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} ==>
             accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
             no_start_coll AKE_EexpRev.evs{2} /\
             no_accept_coll AKE_EexpRev.evs{2} /\
             valid_accepts AKE_EexpRev.evs{2} /\
             inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} /\
             inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
               AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted{2} =>
                in_dom x AKE_EexpRev.mStarted{2}) /\
             ! AKE_Fresh.test = None /\
             mem (Accept (proj AKE_Fresh.test)) AKE_Fresh.evs /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted{2} =>
                ! in_dom x AKE_EexpRev.mCompleted{2} =>
                sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
             AKE_Fresh.test = AKE_EexpRev.test{2} /\
             mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}] = 1%r.
proof strict.
 intros => &2 h; fun.
 inline AKE_Fresh(A).O.computeKey AKE_Fresh(A).O.h2.
 sp; if; last first.
  skip; progress => //.
 
  sp; if; last first.
   wp; skip; progress => //.
    by rewrite mem_cons; right.
  
   wp; rnd; wp; skip; progress => //.
    by rewrite mem_cons; right.
  
   by apply TKey.Dword.lossless.
qed.


local lemma bdh1_sessionRev_2 :
forall &1,
  bd_hoare[ AKE_EexpRev(A).O.sessionRev :
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs ==>
             (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
              collision_eexp_rcvd AKE_EexpRev.evs) /\
             accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
             no_start_coll AKE_EexpRev.evs /\
             no_accept_coll AKE_EexpRev.evs /\
             valid_accepts AKE_EexpRev.evs /\
             inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp /\
             inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
               AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
             (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
             ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mCompleted =>
                in_dom x AKE_EexpRev.mStarted) /\
             ! AKE_Fresh.test{1} = None /\
             mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
             (forall (x : Sidx),
                in_dom x AKE_EexpRev.mStarted =>
                ! in_dom x AKE_EexpRev.mCompleted =>
                sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
             AKE_Fresh.test{1} = AKE_EexpRev.test /\
             mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs] = 1%r.
proof strict.
 intros => &1; fun.
 inline AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2.
 sp; if; last first.
  skip; progress => //.
 
  sp; if; last first.
   wp; skip; progress => //.

  elim H => h; last first.
   by right; apply collision_eexp_rcvd_mon.
  cut heq_tf :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq_tf //.
  intros => h.
  case (collision_eexp_rcvd (SessionRev
     (compute_sid AKE_EexpRev.mStarted{hr} AKE_EexpRev.mEexp{hr}
        AKE_EexpRev.mCompleted{hr} i{hr}) :: evsR)) => hcoll; 
   first by right.
  left.
  apply coll_fresh => //.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  by rewrite mem_cons; right.

  wp; rnd; wp; skip; progress => //.
  elim H => h; last first.
   by right; apply collision_eexp_rcvd_mon.
  cut heq_tf :
   forall t ev,  t <> None =>  test_fresh t ev = fresh (proj t) ev by smt.
  generalize h.
  rewrite !heq_tf //.
  intros => h.
  case (collision_eexp_rcvd (SessionRev
     (compute_sid AKE_EexpRev.mStarted{hr} AKE_EexpRev.mEexp{hr}
        AKE_EexpRev.mCompleted{hr} i{hr}) :: evsR)) => hcoll; 
   first by right.
  left.
  apply coll_fresh => //.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  by rewrite mem_cons; right.
  by apply TKey.Dword.lossless.
save.
 
local equiv eq1_guess :
    AKE_Fresh(A).A.guess ~ AKE_EexpRev(A).A.guess :
if ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) then 
(  ={k, glob A} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  ! AKE_Fresh.test{1} = None /\
  mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll AKE_EexpRev.evs{2} /\
  no_accept_coll AKE_EexpRev.evs{2} /\
  valid_accepts AKE_EexpRev.evs{2} /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2} /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
    AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
  (forall (x : Sidx),
     in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall (x : Sidx),
    in_dom x AKE_EexpRev.mStarted{2} =>
    ! in_dom x AKE_EexpRev.mCompleted{2} =>
    sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}) else
(   AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\  
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2})
==>
  if ! (! test_fresh AKE_EexpRev.test{2} AKE_EexpRev.evs{2} \/
     collision_eexp_rcvd AKE_EexpRev.evs{2}) then
    ={res} /\
    AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2} else 
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}.
proof strict.
 fun (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/
     collision_eexp_rcvd AKE_EexpRev.evs)
    (AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
    AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
    AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
    AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
    AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
    AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
    AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
    AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
    AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
    AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2})
   (accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
    no_start_coll AKE_EexpRev.evs{2} /\
    no_accept_coll AKE_EexpRev.evs{2} /\
    valid_accepts AKE_EexpRev.evs{2} /\
    inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} /\
    inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
      AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
    AKE_Fresh.test{1} <> None /\
    mem (Accept (proj AKE_Fresh.test{1})) AKE_Fresh.evs{1} /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted{2} =>
      ! in_dom x AKE_EexpRev.mCompleted{2} =>
      sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
    AKE_Fresh.test{1} = AKE_EexpRev.test{2} /\
   mem (Accept (proj AKE_EexpRev.test{2})) AKE_EexpRev.evs{2}).
smt.
smt.
by apply A_Lossless_guess.
by apply eq1_eexpRev.
by apply bdh1_eexpRev1.
by apply bdh1_eexpRev2.
by apply eq1_h2_a.
by apply bdh1_h2_a_1.
by apply bdh1_h2_a_2.
by apply eq1_init1.
by apply bdh1_init11.
by apply bdh1_init1_2.
by apply eq1_init2.
by apply bdh1_init2_1.
by apply bdh1_init2_2.
by apply eq1_resp.
by apply bdh1_resp_1.
by apply bdh1_resp_2.
by apply eq1_staticRev.
by apply bdh1_staticRev_1.
by apply bdh1_staticRev_2.
by apply eq1_sessionRev.
by apply bdh1_sessionRev_1.
by apply bdh1_sessionRev_2.
save.



local equiv Eq_AKE_EexpRev_AKE_no_collision :
 AKE_Fresh(A).main ~ AKE_EexpRev(A).main  :
={glob A} ==> 
(res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)){2}
=>
(res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs) ){1}.
fun.
 seq 14 14:(={b,pks,t_idx,key,keyo,b',i,pks, glob A} /\
  AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  AKE_EexpRev.evs{2} = [] /\ 
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
  AKE_Fresh.test{1} = None /\
 AKE_Fresh.mStarted{1} = Map.empty /\
 AKE_Fresh.mCompleted{1} = Map.empty).
 inline AKE_Fresh(A).init AKE_EexpRev(A).init.
 while
(  ={sidxs} /\
AKE_Fresh.mEexp{1} = AKE_EexpRev.mEexp{2}  /\
  (forall (s : Sidx), !mem s sidxs{2} => in_dom s AKE_EexpRev.mEexp{2})). 
wp; rnd; wp; skip; progress; try smt.
case  (s = (pick sidxs{2})) => h.
 by rewrite h;apply in_dom_setE.
generalize H5; rewrite mem_rm !not_and => [hl|]; last by smt.
 by cut:= H s _ => //;rewrite in_dom_setNE //.
while (={pks, i} /\ AKE_Fresh.mSk{1} = AKE_EexpRev.mSk{2}).
by wp; rnd.
by wp; skip; progress => //; smt.
  if{1}; last first.

(* if we have a collision after sampling the eph secrets, it suffices to
   show preservation of collisions *)
  conseq (_ : collision_eexp_eexp_op AKE_EexpRev.mEexp{2} ==> 
              collision_eexp_eexp_op AKE_EexpRev.mEexp{2}).
  smt.
  smt.
cut hh2 : bd_hoare
 [AKE_EexpRev(A).O.h2 : 
  collision_eexp_eexp_op AKE_EexpRev.mEexp ==> 
  collision_eexp_eexp_op AKE_EexpRev.mEexp] = 1%r.
 by fun; wp; rnd; skip; progress => //; apply TKey.Dword.lossless.

cut hck : bd_hoare
 [AKE_EexpRev(A).O.computeKey : 
  collision_eexp_eexp_op AKE_EexpRev.mEexp ==> 
  collision_eexp_eexp_op AKE_EexpRev.mEexp] = 1%r.
 by fun; sp; if; wp; try call hh2; wp.
 seq 0 2: (collision_eexp_eexp_op AKE_EexpRev.mEexp{2}).
 rnd{2}.
 call{2}(_ : (collision_eexp_eexp_op AKE_EexpRev.mEexp) ==>
            (collision_eexp_eexp_op AKE_EexpRev.mEexp)).

 fun (collision_eexp_eexp_op AKE_EexpRev.mEexp).
 smt.
 smt.
 progress; apply (A_Lossless_choose O) => //.
 by fun; wp.
 by fun; wp. 
 by fun; wp.
 by fun; wp.
 by fun; wp. 
 by fun; sp; if; wp; try call hh2; wp => //.
 by fun; sp; if; try call hck; wp.
 skip; progress; smt.
 

 if{2}; last by trivial.
 call{2}(_ : (collision_eexp_eexp_op AKE_EexpRev.mEexp) ==>
            (collision_eexp_eexp_op AKE_EexpRev.mEexp)).
 fun (collision_eexp_eexp_op AKE_EexpRev.mEexp).
 smt.
 smt.
 by apply A_Lossless_guess.
 by fun; wp.
 by fun; sp; if; wp; try call hh2; wp => //.
 by fun; wp. 
 by fun; wp.
 by fun; wp.
 by fun; wp.
 by fun; sp; if; try call hck; wp.
 sp; if{2}; wp; [call{2} hck | rnd{2} ]; skip; smt.
seq 2 2:
( ={b, pks, t_idx, key, keyo, b', i, pks, glob A} /\
AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
  AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
  AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  AKE_Fresh.test{1} = None /\
  accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
  no_start_coll(AKE_EexpRev.evs{2}) /\
  no_accept_coll(AKE_EexpRev.evs{2}) /\
  valid_accepts (AKE_EexpRev.evs{2}) /\
  inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} AKE_EexpRev.mEexp{2}  /\
  inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2} 
             AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
  (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\ 
  (forall x, in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
  (forall x, in_dom x AKE_EexpRev.mStarted{2} => !in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj (AKE_EexpRev.mStarted{2}.[x])) = init)).
rnd.
call eq1_choose.
wp; skip; progress; try assumption.  
   rewrite /accept_evs_eexps; smt.
   smt.
   rewrite /no_start_coll => X A1 A2 B1 B2 r1 r2 i j hpos1 hpos2.
   rewrite nth_geq_len ?length_nil //; smt.
   rewrite /no_accept_coll => X A1 A2 B1 B2 Y1 Y2 r1 r2 i j hpos1 hpos2.
   rewrite nth_geq_len ?length_nil //; smt.
   rewrite /valid_accepts => s i; rewrite length_nil; smt.
   rewrite /inv_started => ps; split.
    cut:= mem_nil (Start ps); smt.
    smt.
   rewrite /inv_accepted => ps; split.
    cut:= mem_nil (Accept ps); smt.
    smt.
  smt.
  smt.
  if{1}.
  rcondt{2} 1.
  intros => &m; skip; progress => //.
seq 2 2:
  ((={b, pks, t_idx, key, keyo, b', i, pks, glob A, keyo} /\
   AKE_EexpRev.evs{2} = AKE_Fresh.evs{1} /\
   AKE_EexpRev.test{2} = AKE_Fresh.test{1} /\
   AKE_EexpRev.cSession{2} = AKE_Fresh.cSession{1} /\
   AKE_EexpRev.cH2{2} = AKE_Fresh.cH2{1} /\
   AKE_EexpRev.mH2{2} = AKE_Fresh.mH2{1} /\
   AKE_EexpRev.sH2{2} = AKE_Fresh.sH2{1} /\
   AKE_EexpRev.mSk{2} = AKE_Fresh.mSk{1} /\
   AKE_EexpRev.mEexp{2} = AKE_Fresh.mEexp{1} /\
   AKE_EexpRev.mStarted{2} = AKE_Fresh.mStarted{1} /\
   AKE_EexpRev.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
   AKE_Fresh.test{1} = Some (compute_sid AKE_Fresh.mStarted{1} 
     AKE_Fresh.mEexp{1} AKE_Fresh.mCompleted{1} t_idx{2}) /\
   accept_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
   start_evs_eexps AKE_EexpRev.evs{2} AKE_EexpRev.mEexp{2} /\
   no_start_coll AKE_EexpRev.evs{2} /\
   no_accept_coll AKE_EexpRev.evs{2} /\
   valid_accepts AKE_EexpRev.evs{2} /\
   inv_started AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
     AKE_EexpRev.mEexp{2} /\
   inv_accepted AKE_EexpRev.evs{2} AKE_EexpRev.mStarted{2}
     AKE_EexpRev.mEexp{2} AKE_EexpRev.mCompleted{2} /\
   (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp{2}) /\
   ! collision_eexp_eexp_op AKE_EexpRev.mEexp{2} /\
   (forall (x : Sidx),
      in_dom x AKE_EexpRev.mCompleted{2} => in_dom x AKE_EexpRev.mStarted{2}) /\
   (forall (x : Sidx),
     in_dom x AKE_EexpRev.mStarted{2} =>
     ! in_dom x AKE_EexpRev.mCompleted{2} =>
     sd2_role (proj AKE_EexpRev.mStarted{2}.[x]) = init) /\
  ! AKE_Fresh.mStarted{1}.[t_idx{1}] = None &&
  ! AKE_Fresh.mCompleted{1}.[t_idx{1}] = None)).
  sp; (if; first smt); last first.
  wp; rnd; skip; progress => //.
inline AKE_Fresh(A).O.computeKey AKE_EexpRev(A).O.computeKey
       AKE_Fresh(A).O.h2 AKE_EexpRev(A).O.h2. 
sp; if => //.

wp; rnd; wp; skip; progress => //.

wp; skip; progress => //.
call eq1_guess.
skip; progress => //.
smt.
  rewrite proj_some.
  cut [h1 h2] := H5 (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
        AKE_Fresh.mCompleted{1} t_idx{2}).
  apply h2.
  exists t_idx{2}; progress => //.
   by apply H6.
  rewrite proj_some.
  cut [h1 h2] := H5 (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
          AKE_Fresh.mCompleted{1} t_idx{2}).
  apply h2.
  exists t_idx{2}; progress => //.
   by apply H6.
   smt.

  rewrite proj_some.
  cut [h1 h2] := H5 (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
        AKE_Fresh.mCompleted{1} t_idx{2}).
  apply h2.
  exists t_idx{2}; progress => //.
  by apply H6.
  cut [h1 h2] := H5 (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
          AKE_Fresh.mCompleted{1} t_idx{2}).
  rewrite proj_some;apply h2.
  exists t_idx{2}; progress => //.
   by apply H6.
   smt.
   smt.   
   elim H13; progress => //.
   smt.
 elim H17.
smt.
smt.
smt.
if{2} => //.
sp.
conseq (_ :   (! AKE_EexpRev.test = None /\
    mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs /\
    accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    no_start_coll AKE_EexpRev.evs /\
    no_accept_coll AKE_EexpRev.evs /\
    valid_accepts AKE_EexpRev.evs /\
    inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp /\
    inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted => in_dom x AKE_EexpRev.mStarted) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted =>
      ! in_dom x AKE_EexpRev.mCompleted =>
      sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
      (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/ 
        collision_eexp_rcvd AKE_EexpRev.evs)){2} ==>
   (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/ 
        collision_eexp_rcvd AKE_EexpRev.evs){2}).
progress => //.
 by smt.
 rewrite proj_some.
   cut [h1 h2] := H5 (compute_sid AKE_Fresh.mStarted{1} AKE_Fresh.mEexp{1}
        AKE_Fresh.mCompleted{1} t_idx{2}).
   apply h2 => {h2}{h1}.
   by exists t_idx{2}; progress => //; apply H6.
 by left; rewrite /test_fresh not_and;right; rewrite fresh_op_def'; smt.
smt.
call{2} 
(_ : 
    ! AKE_EexpRev.test = None /\
    mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs /\
    accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    no_start_coll AKE_EexpRev.evs /\
    no_accept_coll AKE_EexpRev.evs /\
    valid_accepts AKE_EexpRev.evs /\
    inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp /\
    inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted => in_dom x AKE_EexpRev.mStarted) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted =>
      ! in_dom x AKE_EexpRev.mCompleted =>
      sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
      (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/ 
        collision_eexp_rcvd AKE_EexpRev.evs)==>
    ! AKE_EexpRev.test = None /\
    mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs /\
    accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    no_start_coll AKE_EexpRev.evs /\
    no_accept_coll AKE_EexpRev.evs /\
    valid_accepts AKE_EexpRev.evs /\
    inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp /\
    inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted => in_dom x AKE_EexpRev.mStarted) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted =>
      ! in_dom x AKE_EexpRev.mCompleted =>
      sd2_role (proj AKE_EexpRev.mStarted.[x]) = init) /\
      (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/ 
        collision_eexp_rcvd AKE_EexpRev.evs)).
fun ((! AKE_EexpRev.test = None /\
    mem (Accept (proj AKE_EexpRev.test)) AKE_EexpRev.evs /\
    accept_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    start_evs_eexps AKE_EexpRev.evs AKE_EexpRev.mEexp /\
    no_start_coll AKE_EexpRev.evs /\
    no_accept_coll AKE_EexpRev.evs /\
    valid_accepts AKE_EexpRev.evs /\
    inv_started AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp /\
    inv_accepted AKE_EexpRev.evs AKE_EexpRev.mStarted
      AKE_EexpRev.mEexp AKE_EexpRev.mCompleted /\
    (forall (s : Sidx), in_dom s AKE_EexpRev.mEexp) /\
    ! collision_eexp_eexp_op AKE_EexpRev.mEexp /\
    (forall (x : Sidx),
       in_dom x AKE_EexpRev.mCompleted => in_dom x AKE_EexpRev.mStarted) /\
    (forall (x : Sidx),
      in_dom x AKE_EexpRev.mStarted =>
      ! in_dom x AKE_EexpRev.mCompleted =>
      sd2_role (proj AKE_EexpRev.mStarted.[x]) = init)) &&
     (! test_fresh AKE_EexpRev.test AKE_EexpRev.evs \/ 
        collision_eexp_rcvd AKE_EexpRev.evs)) => //.
apply A_Lossless_guess.

fun; wp; skip; progress => //.
  by rewrite mem_cons; right.
  by apply accept_evs_eexps_pres; smt.
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.
  by apply inv_accepted_pres => //; smt.
  apply coll_or_not_fresh_test_mon_ev => //.

fun; sp; if; inline AKE_EexpRev(A).O.h2; wp; try rnd; wp; skip; progress => //.
  by apply TKey.Dword.lossless.

fun; wp; skip; progress => //.
  by rewrite mem_cons; right.
  by apply accept_evs_eexps_pres; smt. 
  by apply start_evs_eexps_pres_ev => //; smt.
  apply no_start_coll_pres_ev => //.
    intros s' hmem; apply not_def => h'.
    elim (H6 s') => [hl hr] {hr}.
    elim (hl _) => // j [hstarted][hdom]heq' {hl}.
    cut hneq:  j <> i{hr}; first by apply not_def => heq''; 
      generalize H12 hstarted; rewrite heq''.
    generalize heq'; 
    elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => A B r /= heq1.
    apply not_def => [[heq2 hrole']].
    generalize h'; rewrite heq2 /psid_sent /=; apply not_def => {heq2}{heq1} heq1.
    cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
    rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
    exists i{hr}; exists j; do !split => //.
    apply H8.
    cut: (proj AKE_EexpRev.mEexp{hr}.[i{hr}]) =
         (proj AKE_EexpRev.mEexp{hr}.[j]); first by apply gen_epk_inj.
    cut h':= H8 i{hr} => h''.
    apply proj_inj_some.
     by generalize h''; rewrite /in_dom.
     by generalize hdom; rewrite /in_dom.
     by rewrite h''.
     by smt.

  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres_ev => //; apply H8 => //.
  apply inv_accepted_pres_ev2 => //.
   by apply not_def => h; cut: in_dom i{hr} AKE_EexpRev.mStarted{hr}; try apply H10; smt.
   by smt.

  by rewrite in_dom_set; left; apply H10.
  generalize H16; rewrite in_dom_set => [ hdom | ->]; [rewrite get_setNE // | rewrite get_setE].
   by apply not_def => abs; generalize hdom H15; rewrite abs; smt.
   by apply H11.
   by rewrite /sd2_role proj_some.

  apply coll_or_not_fresh_test_mon_ev => //.

fun; wp; skip; progress => //.
  by rewrite mem_cons; right.

  apply accept_evs_eexps_pres_ev => //.
   exists i{hr}; do !split => //.
   apply H8 => //.
   rewrite  /sid_sent /compute_sid /= get_setE proj_some /=.
   by elim /tuple3_ind  (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /=.
  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt. 
  apply no_accept_coll_pres_ev => //.
   intros => s hmem.
   rewrite /compute_sid get_setE.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /=;
    rewrite {1}/sid_sent /= => A B r heq';apply not_def => h'.
   cut [h1 h2]:= H7 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq''.
   generalize  heq'' h' => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq''.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq'''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H8.
      apply proj_inj_some.
       by cut:= H8 i{hr}; rewrite /in_dom.
       by cut:= H8 j; rewrite /in_dom.
       by apply gen_epk_inj.
 
  apply valid_accept_pres_ev => //.   
    rewrite /psid_of_sid/compute_sid get_setE.
    elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[i{hr}]) => /= A' B' r' heq'.
    cut [h1 h2]:=
    H6 (A', B', gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), r') => {h1}.
    apply h2.
    exists i{hr}; rewrite heq'; progress => //.
     by apply H8.
     by cut:= H11 i{hr} _ _ => //; rewrite heq' /sd2_role /=.

  by apply inv_started_pres => //; smt.          
  apply inv_accepted_pres_ev1 => //.
    by apply H8.
    case (x = i{hr}).
     by intros ->.
     by intros neq; generalize H15; rewrite in_dom_setNE // => h; apply H10.
    case (x = i{hr}).
     by intros => ->; cut:= H11 i{hr} _ _.
     by intros => hneq; apply H11 => //; generalize H16; rewrite in_dom_set; smt.

  apply coll_or_not_fresh_test_mon_ev => //.

fun; wp; skip; progress => //.
  by rewrite mem_cons; right.
  apply accept_evs_eexps_pres_ev => //.
    by rewrite /sid_sent /=; exists i{hr}; split; smt.

  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  apply no_accept_coll_pres_ev => //.
   intros => s hmem; rewrite {1}/sid_sent /=.
   apply not_def => heq.
   cut [h1 h2]:= H7 s => {h2}.
   elim (h1 _) => //. 
   intros => {h1} j [hjstrt][hjcomp][heexp] heq'.
   generalize  heq' heq => ->; rewrite /sid_sent /compute_sid /=.
   elim /tuple3_ind (proj AKE_EexpRev.mStarted{hr}.[j]) => /= A' B' r' heq'.
   case (i{hr} = j) => hor.
     by generalize hjstrt H10; rewrite hor; smt.

     apply not_def => heq''; 
     cut: collision_eexp_eexp_op AKE_EexpRev.mEexp{hr}; last by smt.
     rewrite collision_eexp_eexp_op_def /collision_eexp_eexp.
     exists i{hr}; exists j; do !split => //.
      by apply H8.
      apply proj_inj_some.
       by cut:= H8 i{hr}; rewrite /in_dom.
       by cut:= H8 j; rewrite /in_dom.
       by apply gen_epk_inj. 
  
  by apply valid_accept_pres_ev2.

  rewrite /inv_started.
  intros => ps; rewrite mem_cons; split.
   intros => [|] hor.
   smt.
   cut [h1 h2 ]:= H6 ps => {h2}.
    elim (h1 _) => // j [hdom1'][hdom2'] heq.
   case (j = i{hr}) => heq'.
     by generalize heq' H15 hdom1' => ->; smt.
     exists j; progress => //.
     rewrite in_dom_setNE //.
     generalize H17 heq; (rewrite get_setNE; first by smt) => -> //.
     generalize H17 heq; (rewrite get_setNE; first by smt) => -> //.

   intros => [j][hdom1][hdom2] heq.
   case (j = i{hr}) => hor.
    generalize hor heq => ->; rewrite get_setE proj_some /=; smt.
   right.
   cut [h1 h2] := H6 ps; apply h2.
   exists j; progress.
    by generalize hdom1; rewrite in_dom_setNE.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H17 /=.
    by generalize heq; (rewrite get_setNE; first smt); rewrite H17 /=.
   rewrite /inv_accepted => ps; rewrite mem_cons; split.
    intros => [|] hor.
    cut: ps = (B{hr}, A{hr}, gen_epk (proj AKE_EexpRev.mEexp{hr}.[i{hr}]), X{hr},resp).
     by apply Accept_inj.
    intros => ->.
   exists i{hr}; rewrite !in_dom_setE /compute_sid !get_setE !proj_some /=.
    by apply H8.
 
   cut [h1 h2] := H7 ps => {h2}.
   cut:= h1 _ => //; intros => [j][hdom1][hdom2][hdom3] heq.
    case (j = i{hr}) => heq'.
     by generalize heq' H16 hdom1 => ->; smt.
     exists j; (rewrite !in_dom_setNE // /compute_sid heq !get_setNE; first 2 smt).
     by do !split => //.
   intros => [j][hdom1][hdom2][hdom3] heq.
   case (i{hr} = j) => hor.
    generalize heq; rewrite hor.
    by rewrite /compute_sid /= !get_setE !proj_some /= => ->; left.  

   right.
   cut [h1 h2]:= H7 ps => {h1}.
   apply h2.
   exists j.
   generalize hdom1 hdom2 hdom3 heq; 
   rewrite !in_dom_setNE; first 2 smt. 
   by rewrite /compute_sid /= !get_setNE /=; smt.

   generalize H17; rewrite !in_dom_set => [|] hor.
    by left; apply H10.
    by right.
   case (x = i{hr}) => hor.
    by generalize hor H18 => ->; rewrite in_dom_setE.
    rewrite get_setNE; first smt.
    apply H11.
    by generalize H17; rewrite !in_dom_setNE.
    by generalize H18; rewrite !in_dom_setNE. 
  
  apply coll_or_not_fresh_test_mon_ev => //.

fun; wp; skip; progress => //.
  by rewrite mem_cons; right.
  by apply accept_evs_eexps_pres => //; smt.  
  by apply start_evs_eexps_pres => //; smt.
  by apply no_start_coll_pres => //; smt.
  by apply no_accept_coll_pres => //; smt.
  by apply valid_accept_pres => //; smt.
  by apply inv_started_pres => //; smt.  
  by apply inv_accepted_pres => //; smt.  
  apply coll_or_not_fresh_test_mon_ev => //.

fun; sp; if; last first.
  skip; progress => //.

  inline AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2.
    sp; if; last first.
      wp; skip; progress => //. 
      by rewrite mem_cons; right.
      by apply accept_evs_eexps_pres => //; smt.  
      by apply start_evs_eexps_pres => //; smt.
      by apply no_start_coll_pres => //; smt.
      by apply no_accept_coll_pres => //; smt.
      by apply valid_accept_pres => //; smt.
      by apply inv_started_pres => //; smt.  
      by apply inv_accepted_pres => //; smt.  

      apply coll_or_not_fresh_test_mon_ev => //.
 
      wp; rnd; wp; skip; progress => //.
      by rewrite mem_cons; right.
      by apply accept_evs_eexps_pres => //; smt.  
      by apply start_evs_eexps_pres => //; smt.
      by apply no_start_coll_pres => //; smt.
      by apply no_accept_coll_pres => //; smt.
      by apply valid_accept_pres => //; smt.
      by apply inv_started_pres => //; smt.  
      by apply inv_accepted_pres => //; smt.  
      by apply coll_or_not_fresh_test_mon_ev => //.
      by apply TKey.Dword.lossless.

if{2}; last first.
wp; rnd{2}; skip; progress => //.
smt.
inline AKE_EexpRev(A).O.computeKey AKE_EexpRev(A).O.h2.
sp; if{2}.
wp; rnd{2}; wp; skip; progress => //.
smt.
wp; skip; progress => //.
save.

local equiv Eq_AKE_EexpRev_AKE_no_collision' :
 AKE_EexpRev(A).main ~ AKE_Fresh(A).main :
={glob A} ==> 
(res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)){1}
=>
(res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs) ){2}.
proof strict.
 symmetry.
 by conseq Eq_AKE_EexpRev_AKE_no_collision.
save.

local lemma Pr1 : 
forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
Pr[AKE_Fresh(A).main() @ &m : res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs)].
proof strict.
 intros => &m.
 by equiv_deno Eq_AKE_EexpRev_AKE_no_collision'.
save.



local module AKE_NoHashOnCompute(FA : Adv2) = {
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var t_idx : Sidx    
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
      ((test <> None) => 
      fresh_op (proj test) (EphemeralRev(compute_psid mStarted mEexp i)::evs ))) {
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
      if ( in_dom A mSk && in_dom B mSk && !in_dom i mStarted ) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
       (test <> None => 
       fresh_op (proj test) 
        (Accept(compute_sid mStarted mEexp mCompleted.[i<- Y] i)::evs ))) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk &&
      ((test <> None => 
       fresh_op (proj test) (StaticRev A::evs )))) {
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
    fun computeKey'(i : Sidx) : Key option = {
      var r : Key option = None;
      var a : Agent;
      var b : Agent;
      var ro : Role;
      var k : Key;
      if (in_dom i mCompleted) {
        (a,b,ro) = proj mStarted.[i];
        k = $sample_Key; 
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted &&
     ((test <> None) =>
      fresh_op (proj test) (SessionRev
          (compute_sid mStarted mEexp mCompleted i)::evs) )) {
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
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;
    var xa' : Eexp = def;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    t_idx = def;
    init();
    while (i < qAgent) {
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      i = i + 1;
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
      if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None &&
          fresh_op (compute_sid mStarted mEexp mCompleted t_idx) evs) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
      (* the if-condition implies "mem (Accept (proj O.test)) O.evs" *)
      if (b) {
       keyo = O.computeKey'(t_idx);
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

op get_string_from_id (i : Sidx)(mStarted : (Sidx, Sdata2) map)(mCompleted : (Sidx, Epk)   map) mEexp mSk : Sstring =
let (a,b,ro) = proj mStarted.[i] in
gen_sstring (proj mEexp.[i]) (proj mSk.[a]) b (proj mCompleted.[i]) ro.

lemma get_string_pres : 
forall (i : Sidx)(mStarted : (Sidx, Sdata2) map)
(mCompleted : (Sidx, Epk)   map) mEexp mSk j v,
j <> i =>
get_string_from_id i mStarted mCompleted mEexp mSk = 
get_string_from_id i mStarted.[j <- v] mCompleted mEexp mSk.
proof strict.
 by progress; rewrite /get_string_from_id get_setNE.
save.

lemma get_string_pres2 : 
forall (i : Sidx)(mStarted : (Sidx, Sdata2) map)
(mCompleted : (Sidx, Epk)   map) mEexp mSk j v,
j <> i =>
get_string_from_id i mStarted mCompleted mEexp mSk = 
get_string_from_id i mStarted mCompleted.[j <- v] mEexp mSk.
proof strict.
 by progress; rewrite /get_string_from_id get_setNE.
save.

local equiv Eq_AKE_Fresh_AKE_NoHashOnCompute :
 AKE_Fresh(A).main ~ AKE_NoHashOnCompute(A).main  :
={glob A} ==> 
(res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs) ){1} =>
((res /\ test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs
                    /\ ! collision_eexp_eexp(AKE_NoHashOnCompute.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoHashOnCompute.evs)){2} \/
(AKE_NoHashOnCompute.test <> None /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
in_dom 
(get_string_from_id AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted 
  AKE_NoHashOnCompute.mCompleted AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) 
AKE_NoHashOnCompute.mH2)){2}.
fun.
 seq 14 14:(={b,pks,key,keyo,b',i,pks, glob A} /\
  t_idx{1} = AKE_NoHashOnCompute.t_idx{2} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\ 
  (forall x, in_dom x AKE_NoHashOnCompute.mEexp{2})).
 while
(  ={sidxs} /\
AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1}  /\
  (forall (s : Sidx), !mem s sidxs{2} => in_dom s AKE_NoHashOnCompute.mEexp{2})). 
wp; rnd; wp; skip; progress => //.
case  (s = (pick sidxs{2})) => h.
 by rewrite h;apply in_dom_setE.
generalize H5; rewrite mem_rm !not_and => [hl|]; last by smt.
 by cut:= H s _ => //;rewrite in_dom_setNE //.
while (={pks, i} /\ AKE_Fresh.mSk{1} = AKE_NoHashOnCompute.mSk{2}).
by wp; rnd.
by inline AKE_Fresh(A).init AKE_NoHashOnCompute(A).init;
    wp; skip; progress => //; smt.
  if => //; last first.
 skip; progress; smt.
 seq 2 2:(={b,pks,key,keyo,b',i,pks, glob A} /\
  t_idx{1} = AKE_NoHashOnCompute.t_idx{2} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\ 
  (forall x, in_dom x AKE_NoHashOnCompute.mEexp{2})).
 rnd.
 call (_ : 
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.mH2{2} = AKE_Fresh.mH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1}).
 by fun; wp; skip; progress.
 by fun; wp; skip; progress.
 by fun; wp; skip; progress.
 by fun; wp; skip; progress.
 by fun; wp; skip; progress.
 by fun; sp; if => //; wp; 
 inline AKE_Fresh(A).O.h2 AKE_NoHashOnCompute(A).O.h2; wp; rnd;
 wp; skip; progress; smt.

 by fun;
 inline AKE_Fresh(A).O.computeKey AKE_Fresh(A).O.h2 
        AKE_NoHashOnCompute(A).O.computeKey  AKE_NoHashOnCompute(A).O.h2;
 sp; if => //; sp; if => //; wp; try rnd; wp; skip; progress; smt.
 by skip; progress; smt.
 if => //; last first.
 by skip; progress => //; left; smt.
cut h: equiv [  AKE_Fresh(A).O.h2 ~ AKE_NoHashOnCompute(A).O.h2 :
 ! in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
         AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
         AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2})
      AKE_NoHashOnCompute.mH2{2} /\
  ={sstring} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  eq_except AKE_NoHashOnCompute.mH2{2} AKE_Fresh.mH2{1}
    (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
       AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
       AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2}) ==>
 ! in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
         AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
         AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2})
      AKE_NoHashOnCompute.mH2{2} =>
  ={res} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  eq_except AKE_NoHashOnCompute.mH2{2} AKE_Fresh.mH2{1}
    (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
       AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
       AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2}) ].
 fun; wp; rnd; wp; skip; progress => //.
  smt.
  by apply eqe_set.
  generalize H6; rewrite in_dom_set not_or => [h1] h2.
  generalize H4 H5; rewrite /in_dom H0 => //; smt.
  generalize H6; rewrite in_dom_set not_or => [h1] h2.
  generalize H4 H5; rewrite /in_dom H0 => //; smt.
  case (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
           AKE_Fresh.mStarted{1} AKE_Fresh.mCompleted{1} AKE_Fresh.mEexp{1}
           AKE_Fresh.mSk{1} = sstring{2}) => h; first by smt.
  generalize H4 H5; rewrite /in_dom H0 => //; smt.
  case (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
           AKE_Fresh.mStarted{1} AKE_Fresh.mCompleted{1} AKE_Fresh.mEexp{1}
           AKE_Fresh.mSk{1} = sstring{2}) => h; first by smt.
  generalize H4 H5; rewrite /in_dom H0 => //; smt.
  case (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
           AKE_Fresh.mStarted{1} AKE_Fresh.mCompleted{1} AKE_Fresh.mEexp{1}
           AKE_Fresh.mSk{1} = sstring{2}) => h; first by smt.
  by rewrite H0 => //. 
cut h': equiv [  AKE_Fresh(A).O.computeKey ~ AKE_NoHashOnCompute(A).O.computeKey :
 ! in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
         AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
         AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2})
      AKE_NoHashOnCompute.mH2{2} /\
  ={i} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  eq_except AKE_NoHashOnCompute.mH2{2} AKE_Fresh.mH2{1}
    (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
       AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
       AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2}) ==>
 ! in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
         AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
         AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2})
      AKE_NoHashOnCompute.mH2{2} =>
  ={res} /\
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
  eq_except AKE_NoHashOnCompute.mH2{2} AKE_Fresh.mH2{1}
    (get_string_from_id AKE_NoHashOnCompute.t_idx{2}
       AKE_NoHashOnCompute.mStarted{2} AKE_NoHashOnCompute.mCompleted{2}
       AKE_NoHashOnCompute.mEexp{2} AKE_NoHashOnCompute.mSk{2}) ].
by fun; sp; if => //; wp; call h; wp; skip; progress => //; smt.
 call ( _ : 
  in_dom 
    (get_string_from_id AKE_NoHashOnCompute.t_idx
       AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
       AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
  AKE_NoHashOnCompute.mH2,
  AKE_NoHashOnCompute.evs{2} = AKE_Fresh.evs{1} /\
  AKE_NoHashOnCompute.test{2} = AKE_Fresh.test{1} /\
  AKE_NoHashOnCompute.cSession{2} = AKE_Fresh.cSession{1} /\
  AKE_NoHashOnCompute.cH2{2} = AKE_Fresh.cH2{1} /\
  AKE_NoHashOnCompute.sH2{2} = AKE_Fresh.sH2{1} /\
  AKE_NoHashOnCompute.mSk{2} = AKE_Fresh.mSk{1} /\
  AKE_NoHashOnCompute.mEexp{2} = AKE_Fresh.mEexp{1} /\
  AKE_NoHashOnCompute.mStarted{2} = AKE_Fresh.mStarted{1} /\
  AKE_NoHashOnCompute.mCompleted{2} = AKE_Fresh.mCompleted{1} /\
Map.eq_except AKE_NoHashOnCompute.mH2{2} AKE_Fresh.mH2{1} 
(get_string_from_id AKE_NoHashOnCompute.t_idx
       AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
       AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk){2} /\ 
in_dom AKE_NoHashOnCompute.t_idx{2} AKE_NoHashOnCompute.mStarted{2} /\
in_dom AKE_NoHashOnCompute.t_idx{2} AKE_NoHashOnCompute.mCompleted{2},
in_dom AKE_NoHashOnCompute.t_idx{2} AKE_NoHashOnCompute.mStarted{2} /\
in_dom AKE_NoHashOnCompute.t_idx{2} AKE_NoHashOnCompute.mCompleted{2}
).
 by apply A_Lossless_guess. 

 by fun; wp; skip; progress.
 by intros => &2 hdom; fun; wp; skip.
 by intros => &1; fun; wp; skip. 

 by fun; sp; if => //; wp; call h; wp; skip; progress => //; smt.
 by intros => &2 hdom; fun; sp; if; inline AKE_Fresh(A).O.h2; 
 wp; try rnd; wp; skip; progress; try apply TKey.Dword.lossless.
 intros => &1; fun; sp; if; inline AKE_NoHashOnCompute(A).O.h2; 
 wp.
 conseq (_ : _ ==> 
 (if ! in_dom sstring0 AKE_NoHashOnCompute.mH2 then
    in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
      AKE_NoHashOnCompute.mH2 \/ (get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) = sstring0
  else
    in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
      AKE_NoHashOnCompute.mH2) /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted) => //.
by intros &hr; rewrite in_dom_set; smt.
rnd; wp; skip; progress => //; first by left.
 by apply TKey.Dword.lossless.
skip; smt.

fun; wp; skip; progress => //.
 case (AKE_NoHashOnCompute.t_idx{2} = i{2}) => heq.
  by generalize H1 H5; rewrite heq; smt.
  by rewrite in_dom_set; left.
  by rewrite -get_string_pres => //; smt.
  by rewrite in_dom_set; left.

by intros => &2 hdom; fun; wp; skip; progress.
intros => &1; fun; wp; skip; progress => //.
case (i{hr} = AKE_NoHashOnCompute.t_idx{hr}) => heq.
 by generalize H0 H4; rewrite -heq; smt.
 by rewrite -get_string_pres.
 by rewrite in_dom_set; left.

fun; wp; skip; progress => //.
by rewrite in_dom_set; left.
case (i{2} = AKE_NoHashOnCompute.t_idx{2}) => heq.
  by generalize H0 H4; rewrite -heq; smt.
  by rewrite -get_string_pres2.
  by rewrite in_dom_set; left.

by intros => &2 hdom; fun; wp; progress.
intros => &1; fun; wp; skip; progress => //.
case (i{hr} = AKE_NoHashOnCompute.t_idx{hr}) => heq.
 by generalize H1 H2; rewrite -heq; smt.
 by rewrite -get_string_pres2.
 by rewrite in_dom_set; left.

fun; wp; skip; progress => //.
  by rewrite in_dom_set; left.
  by rewrite in_dom_set; left.
 case (i{2} = AKE_NoHashOnCompute.t_idx{2}) => heq.
  by generalize H0 H4; rewrite -heq; smt.
  by rewrite -get_string_pres // -get_string_pres2 //.
  by rewrite in_dom_set; left.
  by rewrite in_dom_set; left.
  
by intros => &2 hdom; fun; wp; skip; progress => //.

intros => &1; fun; wp; skip; progress => //.
case (i{hr} = AKE_NoHashOnCompute.t_idx{hr}) => heq.
 by generalize H1 H2; rewrite -heq; smt.
 by rewrite -get_string_pres // -get_string_pres2.
 by rewrite in_dom_set; left.
 by rewrite in_dom_set; left.

by fun; wp; skip; progress.
by intros => &2 hdom; fun; wp; skip; progress => //.
by intros => &1; fun; wp; skip; progress => //.

by fun; sp; if => //; call h'; wp; skip; progress => //; smt.
by intros => &2 hdom; fun; inline AKE_Fresh(A).O.computeKey AKE_Fresh(A).O.h2;
   sp; if; sp; try if; wp; try rnd; wp; skip; progress => //; 
   try apply TKey.Dword.lossless.

intros => &2; fun; inline AKE_NoHashOnCompute(A).O.computeKey 
   AKE_NoHashOnCompute(A).O.h2; sp; if; sp; try if; wp.
conseq (_ : _ ==>
if ! in_dom sstring AKE_NoHashOnCompute.mH2 then
    (in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
      AKE_NoHashOnCompute.mH2 \/ ((get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) = sstring)) /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted
  else
    in_dom
      (get_string_from_id AKE_NoHashOnCompute.t_idx
         AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
         AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
      AKE_NoHashOnCompute.mH2 /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\
    in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted).
by intros => &hr; rewrite in_dom_set; progress.

by rnd; wp; skip; progress => //; try apply TKey.Dword.lossless; smt.
by skip; progress => //.
by wp; skip; progress => //.

(* finished upto call *)
intros => {h} {h'}.
sp; if => //.
inline AKE_Fresh(A).O.computeKey AKE_Fresh(A).O.h2
       AKE_NoHashOnCompute(A).O.computeKey' AKE_NoHashOnCompute(A).O.h2.
sp; if => //.
wp; rnd; wp; skip; progress => //.
by rewrite !get_setE proj_some.
rewrite /eq_except => y heq; rewrite get_setNE.
cut :
 get_string_from_id AKE_NoHashOnCompute.t_idx{2} AKE_Fresh.mStarted{1}
         AKE_Fresh.mCompleted{1} AKE_Fresh.mEexp{1} AKE_Fresh.mSk{1} =
gen_sstring (proj AKE_Fresh.mEexp{1}.[AKE_NoHashOnCompute.t_idx{2}])
    (proj AKE_Fresh.mSk{1}.[x1]) x2
    (proj AKE_Fresh.mCompleted{1}.[AKE_NoHashOnCompute.t_idx{2}]) x3; last by smt.
by rewrite /get_string_from_id; smt.
smt.
elim H10; smt.
generalize H9 H10;rewrite /get_string_from_id; smt.
elim H10; smt.
wp; skip; progress.
generalize H3 H1; rewrite /in_dom; smt.
generalize H3 H1; rewrite /in_dom; smt.
generalize H3 H1; rewrite /in_dom; smt.
generalize H3 H1; rewrite /in_dom; smt.
elim H5; smt.
wp; rnd; skip; progress => //.
elim H7; smt.
save.

local lemma Pr2 : forall &m,
Pr[AKE_Fresh(A).main() @ &m : 
(res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs) )] <=
Pr[AKE_NoHashOnCompute(A).main() @ &m : 
(res /\ test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs
                    /\ ! collision_eexp_eexp(AKE_NoHashOnCompute.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoHashOnCompute.evs) )] +
Pr[AKE_NoHashOnCompute(A).main() @ &m : 
(AKE_NoHashOnCompute.test <> None /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
in_dom 
(get_string_from_id AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted 
  AKE_NoHashOnCompute.mCompleted AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) 
AKE_NoHashOnCompute.mH2)].
proof strict.  
intros => &m.
apply (Real.Trans _ 
 (Pr[AKE_NoHashOnCompute(A).main() @ &m :
   (res /\
   test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs /\
   ! collision_eexp_eexp AKE_NoHashOnCompute.mEexp /\
   ! collision_eexp_rcvd AKE_NoHashOnCompute.evs) \/
   (! AKE_NoHashOnCompute.test = None /\
   in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\
   in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\
   in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
   in_dom
     (get_string_from_id AKE_NoHashOnCompute.t_idx
        AKE_NoHashOnCompute.mStarted AKE_NoHashOnCompute.mCompleted
        AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk)
     AKE_NoHashOnCompute.mH2)]) _).
equiv_deno Eq_AKE_Fresh_AKE_NoHashOnCompute; smt.
rewrite Pr mu_or.
cut h: forall (a b c : real), 0%r <= c => a + b - c <= a + b by smt.
by apply h; smt.
qed.

local module AKE_ComputeRand(FA : Adv2) = {
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var t_idx : Sidx    
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
      ((test <> None) => 
      fresh_op (proj test) (EphemeralRev(compute_psid mStarted mEexp i)::evs ))) {
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
      if ( in_dom A mSk && in_dom B mSk && !in_dom i mStarted ) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
       (test <> None => 
       fresh_op (proj test) 
        (Accept(compute_sid mStarted mEexp mCompleted.[i<- Y] i)::evs ))) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk &&
      ((test <> None => 
       fresh_op (proj test) (StaticRev A::evs )))) {
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
    fun computeKey'(i : Sidx) : Key option = {
      var r : Key option = None;
      var a : Agent;
      var b : Agent;
      var ro : Role;
      var k : Key;
      if (in_dom i mCompleted) {
        (a,b,ro) = proj mStarted.[i];
        k = $sample_Key; 
        r = Some k;
      }
      return r;
    }

    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted &&
     ((test <> None) =>
      fresh_op (proj test) (SessionRev
          (compute_sid mStarted mEexp mCompleted i)::evs) )) {
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
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;
    var xa' : Eexp = def;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    t_idx = def;
    init();
    while (i < qAgent) {
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      i = i + 1;
    }
    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      xa' = $sample_Eexp;
      mEexp.[sidx] = xa';
    } 
    if (!collision_eexp_eexp_op mEexp) {
     t_idx = A.choose(pks);
      if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None &&
          fresh_op (compute_sid mStarted mEexp mCompleted t_idx) evs) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
      (* the if-condition implies "mem (Accept (proj O.test)) O.evs" *)
      key  = $sample_Key;
       keyo = Some key;
      b' = A.guess(keyo);
     }
    }
    b = ${0,1};
    return (b = b');
  }
}.

local equiv AKE_NoHashCall_AKE_ComputeRand : 
AKE_NoHashOnCompute(A).main ~ AKE_ComputeRand(A).main :
={glob A} ==>
(res /\ test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs
                    /\ ! collision_eexp_eexp(AKE_NoHashOnCompute.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoHashOnCompute.evs) ){1} =>
(res ){2}.
proof strict.
 fun.
 seq 14 14:
(={b,pks,key,keyo,b',i,pks, glob A} /\
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1}).
eqobs_in.
if => //.
swap{2} 3 -1.
seq 2 2:
 (={b,pks,key,keyo,b',i,pks, glob A} /\
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1}).
rnd.
call
(_ :
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1}) => //; 
   try (fun; wp; skip; progress => //).

fun; inline AKE_NoHashOnCompute(A).O.h2 AKE_ComputeRand(A).O.h2; 
 sp; if => //; wp; try rnd; wp; skip; progress => //; smt.

fun; inline AKE_NoHashOnCompute(A).O.computeKey AKE_NoHashOnCompute(A).O.h2 
            AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2;
 sp; if => //; sp; if => //; wp; try rnd; wp; skip; progress => //; smt.
if => //.
sp.
call
(_ :
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1}) => //; 
   try (fun; wp; skip; progress => //).

fun; inline AKE_NoHashOnCompute(A).O.h2 AKE_ComputeRand(A).O.h2; 
 sp; if => //; wp; try rnd; wp; skip; progress => //; smt.

fun; inline AKE_NoHashOnCompute(A).O.computeKey AKE_NoHashOnCompute(A).O.h2 
            AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2;
 sp; if => //; sp; if => //; wp; try rnd; wp; skip; progress => //; smt.
if{1}; last by wp; rnd; skip; progress => //.
inline AKE_NoHashOnCompute(A).O.computeKey'.
rcondt{1} 3.
by intros => &m; wp; skip; progress; generalize H0; rewrite /in_dom.
by wp; rnd; wp; skip; progress => //.
by rnd{2}; skip; progress; smt.
qed.

lemma card0_empty : forall (s : 'a FSet.set), card s = 0 => s = FSet.empty.
proof strict.
 intros => s.
 rewrite empty_elems_nil card_def => h.
 by apply length0_nil.
save.

lemma mem_rm_variant : 
forall (s : 'a set), 
s <> FSet.empty =>
card (rm (pick s) s) < card s.
proof strict.
 intros => s hne.
 rewrite card_rm_in;first by apply mem_pick.
 generalize (card s).
 smt.
save.

lemma card_le_0 : forall (s : 'a FSet.set), card s <= 0 => s = FSet.empty.
proof strict.
 intros => s h.
 cut h' : 0 <= card s by (rewrite card_def; apply length_nneg).
 cut _: card s = 0 by smt.
 by apply card0_empty.
save.

local lemma Pr3_aux : forall &m,
Pr[AKE_ComputeRand(A).main() @ &m : res] = 1%r / 2%r.
proof strict.
 intros => &m.
 bdhoare_deno (_ : true ==> _) => //.
 fun.
 rnd ((=) b') => /=.
 inline AKE_ComputeRand(A).init.
 sp.
 seq 3: (true) => //.
 seq 2: (true) => //.
 while (true) (card sidxs) => //=.
 intros => z.
 wp; rnd; wp; skip; progress => //.
 by rewrite card_rm_in;[apply mem_pick | smt].
 by cut:= lossless_sample_Eexp; rewrite /Distr.weight => <-; apply Distr.mu_eq.

 while (i <= qAgent) (qAgent - i) => //=.
 intros => z; wp; rnd; skip; progress => //; first 2 smt.
 by cut:= lossless_sample_Sk; rewrite /Distr.weight => <-; apply Distr.mu_eq.
 skip; progress; first 2 smt.
 
 by apply card_le_0.

 if => //.
 seq 1: true.
 by call (_ : true) => //.
  call (_ : true) => //.
  by progress; apply (A_Lossless_choose O) => //.
  by fun; wp.
  by fun; sp; inline AKE_ComputeRand(A).O.h2; if; wp; try rnd; wp; skip; progress => //; apply TKey.Dword.lossless; smt.
  by fun; wp.
  by fun; wp.
  by fun; wp.
  by fun; sp; inline AKE_ComputeRand(A).O.h2; if; wp; try rnd; wp; skip; progress => //; apply TKey.Dword.lossless; smt.

  by fun; sp; inline AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2; 
   if => //; sp; if => //; wp; try rnd; wp; skip; progress; apply TKey.Dword.lossless; smt.
  (* this is just stupid *)
  conseq (_ : 1 = 1 ==> _).
  if => //.
  call (_ : true).
  by apply A_Lossless_guess.
  by fun; wp.
  by fun; sp; inline AKE_ComputeRand(A).O.h2; if; wp; try rnd; wp; skip; progress => //; apply TKey.Dword.lossless; smt.
  by fun; wp.
  by fun; wp.
  by fun; wp.
  by fun; wp.
  by fun; sp; inline AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2; 
   if => //; sp; if => //; wp; try rnd; wp; skip; progress; apply TKey.Dword.lossless; smt.
  wp; rnd; wp; skip; progress => //.
  apply TKey.Dword.lossless => //.
  trivial.
  smt.
  by skip; progress => //; apply (Bool.Dbool.mu_x_def b'{hr}).
save.

local lemma Pr3 : forall &m,
Pr[AKE_NoHashOnCompute(A).main()@ &m :
(res /\ test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs
                    /\ ! collision_eexp_eexp(AKE_NoHashOnCompute.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoHashOnCompute.evs) )] <= 1%r / 2%r.
proof strict.
 intros => &m.
 apply (Real.Trans _ Pr[AKE_ComputeRand(A).main()@ &m : res] _).
  by equiv_deno AKE_NoHashCall_AKE_ComputeRand.
  by rewrite -(Pr3_aux &m); smt.
save. 

pred invh2 (mH2 : (Sstring, Key) map)  
           (sH2 : Sstring set) evs mStrt mComp mEexp mSk =  
forall x, in_dom x mH2 => 
          (FSet.mem x sH2 \/
           (exists i, in_dom i mComp /\ in_dom i mStrt /\ 
             (List.mem (SessionRev (compute_sid mStrt mEexp mComp i)) evs) /\ 
                      get_string_from_id i mStrt mComp mEexp mSk = x)).
                     

lemma invh2_mon_ev : forall mH2 sH2 evs mStrt mComp mEexp mSk e,
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2 sH2 (e::evs) mStrt mComp mEexp mSk.
proof strict.
 rewrite /invh2; progress => //.
 elim (H x _) => // h.
  by left.
  elim h => i [_][_][_] _.
  by right; exists i; rewrite mem_cons; progress => //; right.
save.

lemma invh2_mon_Strt : forall mH2 sH2 evs mStrt mComp mEexp mSk i v,
! in_dom i mStrt => 
(* ! in_dom i mComp =>  *)
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2 sH2 evs mStrt.[i <- v] mComp mEexp mSk.
proof strict.
 rewrite /invh2.
 intros => mH2 sH2 evs mStrt mCmp mEexp mSk i v hnin_dom h x hd.
 cut:= h x _.
 assumption.
 intros => [_ | [j][hj1][hj2][hj3]hj4] ;[left => // |].
 right; exists j.
 case (i = j) => heq.
  by generalize hnin_dom hj2; rewrite heq; smt.
  by rewrite  /compute_sid /get_string_from_id get_setNE // !in_dom_setNE //; smt.
save.

lemma invh2_mon_Cmp : forall mH2 sH2 evs mStrt mComp mEexp mSk i v,
! in_dom i mComp => 
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2 sH2 evs mStrt mComp.[i <- v] mEexp mSk.
proof strict.
 intros => mH2 sH2 evs mStrt mCmp mEexp mSk i v hnin_dom  h x hd.
 cut := h x _.
 assumption.
 intros => [_ | [j][hj1][hj2][hj3]hj4] ;[left => // |] .
 right; exists j.
 case (i = j) => heq.
  by generalize hnin_dom hj2; rewrite heq; smt.
  by rewrite  /compute_sid /get_string_from_id get_setNE // !in_dom_setNE //; smt.
save.

lemma invh2_mon_h2_1 : forall mH2 sH2 evs mStrt mComp mEexp mSk str v,
!in_dom str mH2 =>
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2.[str <- v] (add str sH2) evs mStrt mComp mEexp mSk.
proof strict.
 rewrite /invh2; progress (rewrite in_dom_set).
  elim H1 => h.
   by elim (H0 x _) => // hmem; rewrite mem_add; [left; left | right].
   by left; rewrite mem_add h; right.
save.  

lemma invh2_mon_h2_2 : forall mH2 sH2 evs mStrt mComp mEexp mSk str,
in_dom str mH2 =>
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2 (add str sH2) evs mStrt mComp mEexp mSk.
proof strict.
 rewrite /invh2; progress. 
  elim (H0 x _) => // h1.
  by rewrite mem_add; left; left.
  by right.
save.

lemma invh2_mon_Rev1 : forall mH2 sH2 evs mStrt mComp mEexp mSk str i A B X v sid,
proj mStrt.[i] = (A, B, X) =>
str = gen_sstring (proj mEexp.[i]) (proj mSk.[A]) B (proj mComp.[i]) X =>
sid = compute_sid mStrt mEexp mComp i =>
! in_dom str mH2 =>
in_dom i mStrt =>
in_dom i mComp =>
invh2 mH2 sH2 evs mStrt mComp mEexp mSk =>
invh2 mH2.[str <- v] sH2  (SessionRev sid :: evs) mStrt mComp mEexp mSk.
proof strict.
 rewrite /invh2; progress.
 generalize H4; rewrite in_dom_set => [|] h.
  cut := H3 x _; first assumption.
  intros => [|] h'; first by left.
  elim h' => j [hj1][hj2][hj3] hj4.
  right; exists j; do! split; try assumption.
  by rewrite mem_cons; right.
  
  right; exists i; do !split => //.
   by rewrite mem_cons; left.
   by rewrite h /get_string_from_id H.
save.


lemma compute_sid_pres_cmp : forall m1 m2 m3 i j v,
j <> i =>
compute_sid m1 m2 m3 i =
compute_sid m1 m2 m3.[j <- v] i.
proof strict.
 intros => m1 m2 m3 i j v hneq.
 by rewrite /compute_sid get_setNE.
save.

lemma compute_sid_pres_strt : forall m1 m2 m3 i j v,
j <> i =>
compute_sid m1 m2 m3 i =
compute_sid m1.[j <- v] m2 m3 i.
proof strict.
 intros => m1 m2 m3 i j v hneq.
 by rewrite /compute_sid get_setNE.
save.


lemma fresh_not_Rev_mem1 : forall s evs,
fresh_op s evs = true =>
! mem (SessionRev s) evs.
proof strict.
 intros => s evs.
 rewrite -fresh_op_def'.
 rewrite /fresh.
 by elim /tuple5_ind s => /= A B X Y r heq; progress.
save.

lemma fresh_not_Rev_mem2 : forall s evs,
fresh_op s evs = true =>
! mem (SessionRev (cmatching s)) evs.
proof strict.
 intros => s evs.
 rewrite -fresh_op_def'.
 rewrite /fresh.
 by elim /tuple5_ind s => /= A B X Y r heq; progress.
save.

lemma fresh_not_Rev1 : forall s t evs,
fresh_op t (SessionRev s :: evs) = true =>
s <> t.
proof strict.
 intros => s t evs.
 rewrite -fresh_op_def'.
 rewrite /fresh.
 elim /tuple5_ind t => /= A B X Y r heq; progress.
 generalize H; rewrite mem_cons not_or.
 smt.
save.

lemma fresh_not_Rev2 : forall s t evs,
fresh_op t (SessionRev s :: evs) = true =>
s <> cmatching t.
proof strict.
 intros => s t evs.
 rewrite -fresh_op_def'.
 rewrite /fresh.
 elim /tuple5_ind t => /= A B X Y r heq; progress.
 generalize H1; rewrite mem_cons not_or.
 smt.
save.


lemma strong_partnering_id :
forall i j mStrt mCmp mEexp mSk,
(forall s, in_dom s mSk => gen_pk(proj mSk.[s]) =  s) =>
in_dom (sid_actor (compute_sid mStrt mEexp mCmp i)) mSk =>
in_dom (sid_actor (compute_sid mStrt mEexp mCmp j)) mSk =>
get_string_from_id i mStrt mCmp mEexp mSk =
get_string_from_id j mStrt mCmp mEexp mSk =>
compute_sid mStrt mEexp mCmp i =
compute_sid mStrt mEexp mCmp j \/
compute_sid mStrt mEexp mCmp i =
cmatching (compute_sid mStrt mEexp mCmp j).
proof strict.
 intros => i j mStrt mCmp mEexp mSk mSk_inv hdom1 hdom2.
 rewrite /get_string_from_id /compute_sid.
 elim /tuple3_ind (proj mStrt.[i]) => A1 B1 r1 /=.
 elim /tuple3_ind (proj mStrt.[j]) => A2 B2 r2 /= heq1 heq2.
 rewrite strong_partnering => [|]; progress.
  rewrite H0 H1.
  cut h: gen_pk (proj mSk.[A1]) = gen_pk (proj mSk.[A2]).
  rewrite H => //.
  generalize h; rewrite !mSk_inv.
   by generalize hdom1; rewrite /sid_actor /compute_sid heq2 /=.
   by generalize hdom2; rewrite /sid_actor /compute_sid heq1 /=.
  by intros => ->; left. 

  rewrite /cmatching /=.
  rewrite H H0.
  rewrite /cmatching /= !mSk_inv.
   by generalize hdom2; rewrite /sid_actor /compute_sid heq1 /=.
   by generalize hdom1; rewrite /sid_actor /compute_sid heq2 /=.
  by right; rewrite (_: r1 = (! r2)); first by smt.
save.

pred valid_start evs = forall A B X r, 
List.mem (Start (A,B,X,r)) evs => 
r = init.

lemma valid_start_pres1 : forall evs e,
(forall ps, Start ps <> e) =>
valid_start evs =>
valid_start (e::evs).
proof strict.
 rewrite /valid_start => evs e h hvalid A B X r; rewrite mem_cons => [|] hs.
 by cut: Start (A, B, X, r) <> e; [ apply h | smt ].
 by apply (hvalid A B X).
save.

lemma valid_start_pres2 : forall evs A B X,
valid_start evs =>
valid_start (Start (A, B, X, init)::evs).
proof strict.
 rewrite /valid_start => evs A B X hvalid A' B' X' r'; rewrite mem_cons => [|] hs.
 cut h:= Start_inj (A', B', X', r') (A, B, X, init) _ => // {hs}.
 smt.
 by apply (hvalid A' B' X' r').
save.

lemma fresh_pres_aux : forall t e evs,
valid_start evs =>
(forall s, SessionRev s <> e) =>
(forall s, StaticRev s <> e) =>
(forall s, EphemeralRev s <> e) =>
(forall A B X Y r, e = Accept (A,B,X,Y,r) => r <> init) => 
fresh_op t evs =>
fresh_op t (e::evs).
proof strict.
 intros => t e evs hvstrt hnsr hnstr hner hneq.
 cut _ : fresh_op t evs = true => fresh_op t (e :: evs) = true; last by smt.
 rewrite -!fresh_op_def' /fresh.
 elim /tuple5_ind t => /= A B X Y r heq.
 progress => //.
  by rewrite mem_cons not_or; split => //; apply hnsr.
  
  generalize H0.
  rewrite !mem_cons !not_and  !not_or => [|] h; [left | right]; split => //.
   by apply hner.
   by apply hnstr.  

  by rewrite mem_cons not_or; split => //; apply hnsr.
  
  generalize H3; rewrite mem_cons => [heqa | hdom].
   by generalize hnstr; rewrite -heqa; smt.
   
   elim (H2 _) => //;intros => [hacc hnoeph|[hsrt hnoex] hnoeph]; [left| right].
    by rewrite mem_cons; right.
    split.
     by rewrite mem_cons; right.
     apply not_def => [[z]]; rewrite mem_cons => [|] h; last first.
     cut: (exists (z : Epk), mem (Accept (B, A, Y, z, ! r)) evs); last by smt.
      by exists z.
     
     generalize hsrt; rewrite /psid_of_sid /cmatching /=.
     apply not_def => h'.
     generalize hvstrt; rewrite /valid_start => hvstrt.
     generalize h.
     cut -> := hvstrt B A Y (!r) _ => //.
     intros heq'.
     by cut := hneq B A Y z init _; first rewrite heq'.

generalize H3.   
rewrite !mem_cons not_or => [ |].
cut : (StaticRev B <> e).
 apply hnstr.
 smt.
intros => _; elim (H2 _) => //.
progress => //. 
by apply hner.
save.


local equiv AKE_NoHashCall_AKE_ComputeRand_bad_ev : 
AKE_NoHashOnCompute(A).main ~ AKE_ComputeRand(A).main :
={glob A} ==>
(AKE_NoHashOnCompute.test <> None /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
in_dom 
(get_string_from_id AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted 
  AKE_NoHashOnCompute.mCompleted AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) 
AKE_NoHashOnCompute.mH2){1} =>
(AKE_ComputeRand.test <> None /\ 
in_dom AKE_ComputeRand.t_idx AKE_ComputeRand.mCompleted /\
mem
(get_string_from_id AKE_ComputeRand.t_idx AKE_ComputeRand.mStarted 
  AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp AKE_ComputeRand.mSk) 
AKE_ComputeRand.sH2 /\
fresh_op (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx) AKE_ComputeRand.evs){2}.
proof strict.
 fun. 
 seq 14 14:
(={b,pks,key,keyo,b',i,pks, glob A} /\
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1} /\
  AKE_ComputeRand.mH2{2} = Map.empty /\
  AKE_ComputeRand.sH2{2} = FSet.empty /\
  AKE_ComputeRand.mCompleted{2} = Map.empty /\
  AKE_ComputeRand.mStarted{2} = Map.empty /\
  AKE_NoHashOnCompute.test{1} = None  /\ 
  (forall i, in_dom i AKE_ComputeRand.mStarted{2} => 
   in_dom (sd2_actor (proj AKE_ComputeRand.mStarted{2}.[i])) 
          AKE_ComputeRand.mSk{2}) /\
  (forall s, in_dom s AKE_ComputeRand.mSk{2} => 
       gen_pk (proj AKE_ComputeRand.mSk{2}.[s]) = s) /\
  valid_start AKE_ComputeRand.evs{2}). 
 while (={sidxs} /\   AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1});
  first by wp; rnd; wp.
 while (={pks, i} /\   AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
(forall s, in_dom s AKE_ComputeRand.mSk{2} => 
       gen_pk (proj AKE_ComputeRand.mSk{2}.[s]) = s)).
wp; rnd; skip; progress.

case (s = gen_pk skaL)=> heq.
 by rewrite heq get_setE proj_some.
 generalize H5; rewrite in_dom_setNE // get_setNE; first smt.
 by intros _; apply H. 

 inline AKE_NoHashOnCompute(A).init AKE_ComputeRand(A).init; wp; skip; progress => //.
 smt.
 smt.
 by rewrite /valid_start; smt.

if => //; last by rnd{2} => //; skip; progress => //; smt.
swap{2} 3 -1.
seq 2 2: (={b,pks,key,keyo,b',i,pks, glob A} /\
  AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1} /\
  (invh2 AKE_ComputeRand.mH2 AKE_ComputeRand.sH2 AKE_ComputeRand.evs 
         AKE_ComputeRand.mStarted AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp 
         AKE_ComputeRand.mSk){2} /\
(forall x, in_dom x AKE_ComputeRand.mCompleted{2} => 
           in_dom x AKE_ComputeRand.mStarted{2} ) /\
  AKE_NoHashOnCompute.test{1} = None  /\
(forall i, in_dom i AKE_ComputeRand.mStarted{2} => 
   in_dom (sd2_actor (proj AKE_ComputeRand.mStarted{2}.[i])) 
          AKE_ComputeRand.mSk{2}) /\
  (forall s, in_dom s AKE_ComputeRand.mSk{2} => 
       gen_pk (proj AKE_ComputeRand.mSk{2}.[s]) = s) /\
  valid_start AKE_ComputeRand.evs{2}).
rnd.
call (_ :
 AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1} /\
  (invh2 AKE_ComputeRand.mH2 AKE_ComputeRand.sH2 AKE_ComputeRand.evs 
         AKE_ComputeRand.mStarted AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp 
         AKE_ComputeRand.mSk){2} /\
 (forall x, in_dom x AKE_ComputeRand.mCompleted{2} => 
           in_dom x AKE_ComputeRand.mStarted{2} ) /\
(forall i, in_dom i AKE_ComputeRand.mStarted{2} => 
   in_dom (sd2_actor (proj AKE_ComputeRand.mStarted{2}.[i])) 
          AKE_ComputeRand.mSk{2}) /\
  (forall s, in_dom s AKE_ComputeRand.mSk{2} => 
       gen_pk (proj AKE_ComputeRand.mSk{2}.[s]) = s) /\
  valid_start AKE_ComputeRand.evs{2}).
fun; wp; skip; progress; (try apply invh2_mon_ev => //); (try apply H0 => //);
     (try apply H1 => //); (try apply H2 => //).
     by apply valid_start_pres1; smt.
     by apply valid_start_pres1; smt.

fun; wp; skip; progress.
  apply invh2_mon_ev.
  by apply invh2_mon_Strt => //. 
  by rewrite in_dom_set; left; apply H0.
  case (i{2} = i0) => heq.
   by rewrite heq get_setE proj_some /sd2_actor /=.
   generalize H7; rewrite get_setNE // in_dom_setNE; first smt.
   by intros h; apply H1.

  by apply valid_start_pres2.

fun; wp; skip; progress.
  apply invh2_mon_ev.
  by apply invh2_mon_Cmp.
  by generalize H7; rewrite in_dom_set => [ h | -> ]; [apply H0 | ].
  by apply valid_start_pres1; smt.

fun; wp; skip; progress.
  apply invh2_mon_ev.
  apply invh2_mon_Cmp.
  assumption.  
  by apply invh2_mon_Strt. 
  by generalize H8; rewrite !in_dom_set => [h | ->]; [left; apply H0 | right].
  case (i{2} = i0) => heq.
   by rewrite heq get_setE proj_some /sd2_actor /=.
   generalize H8; rewrite get_setNE // in_dom_setNE; first smt.
   by intros h; apply H1.
  by apply valid_start_pres1; smt.

fun; wp; skip; progress; try apply H0; try assumption.
  by apply invh2_mon_ev.
  by apply valid_start_pres1; smt.

fun; inline AKE_NoHashOnCompute(A).O.h2 AKE_ComputeRand(A).O.h2; sp; if => //; wp; try rnd; wp; skip; progress => //;(try apply H0 => //);
 (try apply H1 => //); (try apply H2 => //).
 by apply invh2_mon_h2_1.
 by apply invh2_mon_h2_2.
  
fun.
inline AKE_NoHashOnCompute(A).O.computeKey AKE_NoHashOnCompute(A).O.h2 
       AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2.
sp; if => //; sp; try if => //; wp; try rnd; wp; skip; progress.
 apply (invh2_mon_Rev1 _ _ _ _ _ _ _ _ i{2} x1 x2 x3 keL _) => //.
  by apply H0.

 by apply valid_start_pres1; smt.
 by apply invh2_mon_ev.
 by apply valid_start_pres1; smt.
 by apply invh2_mon_ev.
 by apply valid_start_pres1; smt.

skip; progress => //.
 rewrite /invh2; progress; smt.
 smt.
 if => //.
 call (_ :
 AKE_ComputeRand.t_idx{2} = AKE_NoHashOnCompute.t_idx{1} /\
  AKE_ComputeRand.evs{2} = AKE_NoHashOnCompute.evs{1} /\
  AKE_ComputeRand.test{2} = AKE_NoHashOnCompute.test{1} /\
  AKE_ComputeRand.cSession{2} = AKE_NoHashOnCompute.cSession{1} /\
  AKE_ComputeRand.cH2{2} = AKE_NoHashOnCompute.cH2{1} /\
  AKE_ComputeRand.mH2{2} = AKE_NoHashOnCompute.mH2{1} /\
  AKE_ComputeRand.sH2{2} = AKE_NoHashOnCompute.sH2{1} /\
  AKE_ComputeRand.mSk{2} = AKE_NoHashOnCompute.mSk{1} /\
  AKE_ComputeRand.mEexp{2} = AKE_NoHashOnCompute.mEexp{1} /\
  AKE_ComputeRand.mStarted{2} = AKE_NoHashOnCompute.mStarted{1} /\
  AKE_ComputeRand.mCompleted{2} = AKE_NoHashOnCompute.mCompleted{1} /\
  (invh2 AKE_ComputeRand.mH2 AKE_ComputeRand.sH2 AKE_ComputeRand.evs 
         AKE_ComputeRand.mStarted AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp 
         AKE_ComputeRand.mSk){2} /\
 (forall x, in_dom x AKE_ComputeRand.mCompleted{2} => 
           in_dom x AKE_ComputeRand.mStarted{2} ) /\ 
  fresh_op (proj AKE_ComputeRand.test{2}) AKE_ComputeRand.evs{2} /\ 
  in_dom AKE_ComputeRand.t_idx{2} AKE_ComputeRand.mCompleted{2} /\ 
  proj (AKE_NoHashOnCompute.test{1}) = (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx){2} /\ 
! AKE_NoHashOnCompute.test{1} = None /\
(forall i, in_dom i AKE_ComputeRand.mStarted{2} => 
   in_dom (sd2_actor (proj AKE_ComputeRand.mStarted{2}.[i])) 
          AKE_ComputeRand.mSk{2}) /\
  (forall s, in_dom s AKE_ComputeRand.mSk{2} => 
       gen_pk (proj AKE_ComputeRand.mSk{2}.[s]) = s) /\
  valid_start AKE_ComputeRand.evs{2}).
fun; wp; skip; progress; (try apply invh2_mon_ev => //); (try apply H0 => //);(try apply H5 => //);(try apply H6 => //);(try apply H9 => //).
 by apply valid_start_pres1; smt.
 by apply valid_start_pres1; smt.
 
fun; inline AKE_NoHashOnCompute(A).O.h2 AKE_ComputeRand(A).O.h2; sp; if => //; wp; try rnd; wp; skip; progress => //;(try apply H0 => //);
(try apply H5 => //);(try apply H6 => //).
 by apply invh2_mon_h2_1.
 by apply invh2_mon_h2_2.

fun; wp; skip; progress; 
 (try by apply H0); (try by apply H5);
 (try by apply H6); try (by (rewrite mem_cons; smt)); try (by assumption).
  apply invh2_mon_ev.
  by apply invh2_mon_Strt => //. 
  by rewrite in_dom_set; left; apply H0.
  apply fresh_pres_aux; smt.
 
 rewrite -compute_sid_pres_strt; last by assumption.
 by apply not_def => habs; generalize habs H10 => ->; cut:= H0 AKE_NoHashOnCompute.t_idx{1} _.
  case (i{2} = i0) => heq.
   by rewrite heq get_setE proj_some /sd2_actor /=.
   generalize H11; rewrite get_setNE // in_dom_setNE; first smt.
   by intros h; apply H5.
   
   by apply valid_start_pres2.
fun; wp; skip; progress; 
  try (by apply H0);
  try (by apply H5);
  try (by apply H6);
  try (by assumption).
  apply invh2_mon_ev.
  by apply invh2_mon_Cmp.
 
  by  generalize H11; rewrite in_dom_set => [ h | -> ]; [apply H0 | ].
  by apply H10.
  by rewrite in_dom_set; left.
  rewrite  -{1}compute_sid_pres_cmp; last by assumption.

  by apply not_def => heq; generalize heq H8 H2 => ->.
  by apply valid_start_pres1; smt.

  fun; wp; skip; progress; 
  try (by apply H0);
  try (by apply H5);
  try (by apply H6);
  try (by assumption).

  apply invh2_mon_ev.
  apply invh2_mon_Strt; first by assumption.
  by apply invh2_mon_Cmp.
  by generalize H12; rewrite !in_dom_set => [h | ->]; [left; apply H0 | right].
  apply fresh_pres_aux => //; first 3 by smt.

   progress.
   cut H12' := Accept_inj (B{2}, A{2}, gen_epk (proj AKE_NoHashOnCompute.mEexp{1}.[i{2}]), X{2}, resp) (A0, B0, X0, Y, r0) _ => // {H12}.
  smt.
  
  by rewrite in_dom_set; left; assumption.

  rewrite -compute_sid_pres_strt.
  by apply not_def => heq; generalize heq H11 H2 => ->.
  rewrite -compute_sid_pres_cmp; last assumption.
  by apply not_def => heq; generalize heq H11 H2 => ->.

  case (i{2} = i0) => heq.
   by rewrite heq get_setE proj_some /sd2_actor /=.
   generalize H12; rewrite get_setNE // in_dom_setNE; first smt.
   by intros h; apply H5.

  by apply valid_start_pres1; smt.
  
fun; wp; skip; progress; 
  try (by apply H0);
  try (by apply H5);
  try (by apply H6);
  try (by assumption).

  by apply invh2_mon_ev.
  by apply H9.
  by apply valid_start_pres1; smt.

fun;inline AKE_NoHashOnCompute(A).O.computeKey AKE_NoHashOnCompute(A).O.h2 
           AKE_ComputeRand(A).O.computeKey AKE_ComputeRand(A).O.h2.
sp; if => //; sp; try if => //; wp; try rnd; wp; skip; progress;  try (by apply H0);
  try (by apply H5);
  try (by apply H6);
  try (by assumption).

 apply (invh2_mon_Rev1 _ _ _ _ _ _ _ _ i{2} x1 x2 x3 keL _) => //. 
  by apply H0.
 by apply H9.
 by apply valid_start_pres1; smt.
 by apply invh2_mon_ev.
 by apply H9.
 by apply valid_start_pres1; smt.
 by apply invh2_mon_ev.
 by apply H9.
 by apply valid_start_pres1; smt.

sp.
if{1}.
inline AKE_NoHashOnCompute(A).O.computeKey' AKE_NoHashOnCompute(A).O.h2.
sp.
rcondt{1} 1.
by intros => &m; skip; progress; rewrite /in_dom.
wp; rnd; wp.
skip; progress => //;
  try (by apply H0);
  try (by apply H1);
  try (by apply H2);
  try (by assumption).
by rewrite proj_some.
by rewrite proj_some.
smt.
elim (H20 (get_string_from_id AKE_NoHashOnCompute.t_idx{1} mStarted_L
          mCompleted_L AKE_NoHashOnCompute.mEexp{1}
          AKE_NoHashOnCompute.mSk{1}) _) => //.
intros => [i][hi1][hi2][hi3] hi4.
cut:= strong_partnering_id i AKE_NoHashOnCompute.t_idx{1} mStarted_L mCompleted_L
     AKE_NoHashOnCompute.mEexp{1} AKE_NoHashOnCompute.mSk{1} _ _ _ _ => //.

cut := H26 i _ => //.
rewrite /compute_sid /sid_actor /sd2_actor.
by elim /tuple3_ind (proj mStarted_L.[i]) => /= A B r heq.

cut := H26 AKE_NoHashOnCompute.t_idx{1} _ => //.
rewrite /compute_sid /sid_actor /sd2_actor.
by elim /tuple3_ind (proj mStarted_L.[AKE_NoHashOnCompute.t_idx{1}]) => /= A B r heq.

intros => [|] h1.
cut: !mem
       (SessionRev
          (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L i))
       evs_L; last by smt.
generalize H24 H22.
rewrite proj_some => ->;rewrite -h1.
smt.
cut: !mem
       (SessionRev
          (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L i))
       evs_L; last by smt.
generalize H24 H22.
rewrite proj_some => ->; rewrite h1 => habs.
cut : 
fresh_op
        (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L
           AKE_NoHashOnCompute.t_idx{1}) evs_L = true; first smt.
rewrite -fresh_op_def' /fresh.
elim /tuple5_ind  (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L
    AKE_NoHashOnCompute.t_idx{1}) => A B X Y r /=.

by intros => heq; progress.
smt.
wp; rnd; skip; progress; rewrite ?proj_some => //.
smt.

elim (H20 (get_string_from_id AKE_NoHashOnCompute.t_idx{1} mStarted_L
          mCompleted_L AKE_NoHashOnCompute.mEexp{1}
          AKE_NoHashOnCompute.mSk{1}) _) => //.
intros => [i][hi1][hi2][hi3] hi4.
cut:= strong_partnering_id i AKE_NoHashOnCompute.t_idx{1} mStarted_L mCompleted_L
     AKE_NoHashOnCompute.mEexp{1} AKE_NoHashOnCompute.mSk{1} _ _ _ _ => //.

cut := H26 i _ => //.
rewrite /compute_sid /sid_actor /sd2_actor.
by elim /tuple3_ind (proj mStarted_L.[i]) => /= A B r heq.

cut := H26 AKE_NoHashOnCompute.t_idx{1} _ => //.
rewrite /compute_sid /sid_actor /sd2_actor.
by elim /tuple3_ind (proj mStarted_L.[AKE_NoHashOnCompute.t_idx{1}]) => /= A B r heq.

intros => [|] h1.
cut: !mem
       (SessionRev
          (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L i))
       evs_L; last by smt.
generalize H24 H22.
rewrite proj_some => ->;rewrite -h1.
smt.
cut: !mem
       (SessionRev
          (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L i))
       evs_L; last by smt.
generalize H24 H22.
rewrite proj_some => ->; rewrite h1 => habs.
cut : 
fresh_op
        (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L
           AKE_NoHashOnCompute.t_idx{1}) evs_L = true; first smt.
rewrite -fresh_op_def' /fresh.
elim /tuple5_ind  (compute_sid mStarted_L AKE_NoHashOnCompute.mEexp{1} mCompleted_L
    AKE_NoHashOnCompute.t_idx{1}) => A B X Y r /=.

by intros => heq; progress.
generalize H24 H22.
by rewrite proj_some => ->.
save.

local lemma Pr3_bad : forall &m, 
Pr[AKE_NoHashOnCompute(A).main() @ &m : 
AKE_NoHashOnCompute.test <> None /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
in_dom 
(get_string_from_id AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted 
  AKE_NoHashOnCompute.mCompleted AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) 
AKE_NoHashOnCompute.mH2] <=
Pr[AKE_ComputeRand(A).main() @ &m : 
AKE_ComputeRand.test <> None /\ 
in_dom AKE_ComputeRand.t_idx AKE_ComputeRand.mCompleted /\ 
mem
(get_string_from_id AKE_ComputeRand.t_idx AKE_ComputeRand.mStarted 
  AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp AKE_ComputeRand.mSk) 
AKE_ComputeRand.sH2 /\
fresh_op (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx) AKE_ComputeRand.evs].
proof strict.
 intros => &m.
 by equiv_deno AKE_NoHashCall_AKE_ComputeRand_bad_ev.
save.


lemma real_le_plus1 : forall (p q r : real),
p <= q => p + r <= q + r by smt.

lemma real_le_plus : 
forall (p q r s : real), p <= r => q <= s => p + q <= r + s.
proof strict.
 intros => p q r s hle1 hle2.
 apply (Real.Trans _ (r + q) _); first by apply real_le_plus1.
 rewrite (_ : r + q = q + r); first smt.
 rewrite (_ : r + s =  s + r); first smt.
 by apply real_le_plus1.
save.

local lemma Pr_sofar1 : forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
1%r/2%r + 
Pr[AKE_ComputeRand(A).main() @ &m : 
AKE_ComputeRand.test <> None /\ 
in_dom AKE_ComputeRand.t_idx AKE_ComputeRand.mCompleted /\ 
mem
(get_string_from_id AKE_ComputeRand.t_idx AKE_ComputeRand.mStarted 
  AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp AKE_ComputeRand.mSk) 
AKE_ComputeRand.sH2 /\
fresh_op (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx) AKE_ComputeRand.evs].
proof strict. 
 intros => &m.
 apply (Real.Trans _ 
      (Pr[AKE_Fresh(A).main() @ &m : res /\ test_fresh AKE_Fresh.test AKE_Fresh.evs
                    /\ ! collision_eexp_eexp(AKE_Fresh.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_Fresh.evs)]) _).
 apply (Pr1 &m).
 apply (Real.Trans _ 
(Pr[AKE_NoHashOnCompute(A).main() @ &m : 
(res /\ test_fresh AKE_NoHashOnCompute.test AKE_NoHashOnCompute.evs
                    /\ ! collision_eexp_eexp(AKE_NoHashOnCompute.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_NoHashOnCompute.evs) )] +
Pr[AKE_NoHashOnCompute(A).main() @ &m : 
(AKE_NoHashOnCompute.test <> None /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mCompleted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted /\ 
in_dom AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mEexp /\
in_dom 
(get_string_from_id AKE_NoHashOnCompute.t_idx AKE_NoHashOnCompute.mStarted 
  AKE_NoHashOnCompute.mCompleted AKE_NoHashOnCompute.mEexp AKE_NoHashOnCompute.mSk) 
AKE_NoHashOnCompute.mH2)]) _).
 apply (Pr2 &m).
 apply real_le_plus.
 apply (Pr3 &m).
 apply (Pr3_bad &m).
save.


local module AKE_find(FA : Adv2) = {
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cSession, cH1, cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mSk        : (Agent, Sk) map    (* map for static secret keys *)
  var mEexp      : (Sidx, Eexp) map   (* map for ephemeral exponents of sessions *)
  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mKeyRev    : (Sidx, Key) map    (* maps id's to revealed keys *)
  var sKeyRev    : Sidx set           (* set of id's revealed (dom of mKeyrev*)
  var sH2'       : Sstring set        (* exactly dom(mH2) *)
  var t_idx : Sidx  
  
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
    (* AKE_find.sH2' = FSet.empty; *)
    (* AKE_find.sKeyRev = FSet.empty; *)
    (* AKE_find.mKeyRev = Map.empty; *)
  }

  module O : AKE_Oracles2 = {
    
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      if (in_dom i mStarted && 
      ((test <> None) => 
      fresh_op (proj test) (EphemeralRev(compute_psid mStarted mEexp i)::evs ))) {
        evs = EphemeralRev(compute_psid mStarted mEexp i)::evs;
        if (sd2_actor(proj mStarted.[i]) = gen_pk(a)) {
          r = mEexp.[i];
        }
      }
      return r;
    }

   fun eqS(i: Sidx, ss : Sstring) : bool option = {
      var r : bool option = None;
      var ss_i : Sstring;
      var sd : Sdata2;
      var ev : Event;
      if (in_dom i mCompleted && in_dom i mStarted && in_dom i mEexp) {
        (* ev = SessionRev(compute_sid mStarted mEexp mCompleted i); *)
        (* if (! mem ev evs) { evs = ev::evs; } *)
        sd = proj mStarted.[i];
        ss_i = gen_sstring (proj mEexp.[i]) (proj mSk.[sd2_actor sd])
                           (sd2_peer sd) (proj mCompleted.[i])
                           (sd2_role sd);
        r = Some (ss_i = ss);
      }
      return r;
    }
    
    fun find_id (sstr : Sstring, s : Sidx set) : Sidx option = {
      var aux : Sidx set = s;
      var ret = None;
      var i : Sidx = def;
      var b : bool option = None;
      while (aux <> FSet.empty /\ ret = None) {
       i = pick aux;
       aux = rm i aux;
       b = eqS(i, sstr);
       ret = (b <> None && (proj b)) ? Some i : None;
     }
     return ret;
    }
    
    fun h2(sstring : Sstring) : Key = {
      var ke : Key;
      var s : Sidx option = None;
      var ret : Key;
      ke = $sample_Key;
      if (in_dom sstring mH2) {
        ret = proj mH2.[sstring];
      } else {
       s = find_id(sstring, sKeyRev);
       if (s <> None) { ret = proj mKeyRev.[proj s];}
       else {
        ret = ke;
        mH2.[sstring] = ke;
        sH2' = add sstring sH2';
       }
      }
      return ret;
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
      if ( in_dom A mSk && in_dom B mSk && !in_dom i mStarted ) {
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
      if (!in_dom i mCompleted && in_dom i mStarted &&
       (test <> None => 
       fresh_op (proj test) 
        (Accept(compute_sid mStarted mEexp mCompleted.[i<- Y] i)::evs ))) {
        mCompleted.[i] = Y;
        evs = Accept(compute_sid mStarted mEexp mCompleted i)::evs;
      }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (in_dom A mSk &&
      ((test <> None => 
       fresh_op (proj test) (StaticRev A::evs )))) {
        r = mSk.[A];
        evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun find_string (id : Sidx, sstr : Sstring set) : Sstring option = {
      var aux : Sstring set = sstr;
      var ret = None;
      var str : Sstring = def;
      var b : bool option = None;
      while (aux <> FSet.empty /\ ret = None) {
       str = pick aux;
       aux = rm str aux;
       b = eqS(id, str);
       ret = (b <> None && (proj b)) ? Some str : None;
     }
     return ret;
    }
    
    fun find_matching (id : Sidx, id_set : Sidx set) : Sidx option = {
     var sid = compute_sid mStarted mEexp mCompleted id;
     var aux = id_set;
     var ret = None;
     var j : Sidx;
     while (aux <> FSet.empty /\ ret = None) {
      j = pick aux;
      aux = rm j aux;
      if ((compute_sid mStarted mEexp mCompleted j) = sid \/
          cmatching (compute_sid mStarted mEexp mCompleted j) = sid ) ret = Some j;
     }
     return ret;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var k : Key;
      var ret = None;
      var str = None; 
      var j : Sidx option;
      if (in_dom i mCompleted) {
        k = $sample_Key;
        if (in_dom i mKeyRev) {
         ret = mKeyRev.[i];
        } else {
         j = find_matching (i, sKeyRev);
         if (j <> None) {
          ret = mKeyRev.[proj j];
         } else {
          str = find_string (i, sH2');
          if (str <> None) {
           ret = mH2.[proj str];
          } else {
           ret = Some k;
           mKeyRev.[i] = k;
           sKeyRev = add i sKeyRev;
          }
         }
        }
       }
    return ret;
   }


    fun sessionRev(i : Sidx) : Key option = {
      var r : Key option = None;
      if (in_dom i mCompleted &&
     ((test <> None) =>
      fresh_op (proj test) (SessionRev
          (compute_sid mStarted mEexp mCompleted i)::evs) )) {
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
    var key : Key = def;
    var keyo : Key option = def;
    var b' : bool = def;
    var i : int = 0;
    var ska : Sk = def;
    var pka : Pk = def;
    var xa' : Eexp = def;
    var sidxs : Sidx set = univ_Sidx;
    var sidx : Sidx;
    t_idx = def;
    AKE_find.sH2' = FSet.empty;
    AKE_find.sKeyRev = FSet.empty;
    AKE_find.mKeyRev = Map.empty;
    init();
    while (i < qAgent) {
      ska = $sample_Sk;
      pka = gen_pk(ska);
      pks = pka :: pks;
      mSk.[pka] = ska;
      i = i + 1;
    }
    while (sidxs <> FSet.empty) {
      sidx = pick sidxs;
      sidxs = rm sidx sidxs;
      xa' = $sample_Eexp;
      mEexp.[sidx] = xa';
    } 
    if (!collision_eexp_eexp_op mEexp) {
     t_idx = A.choose(pks);
      if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None &&
          fresh_op (compute_sid mStarted mEexp mCompleted t_idx) evs) {
      test = Some (compute_sid mStarted mEexp mCompleted t_idx);
      (* the if-condition implies "mem (Accept (proj O.test)) O.evs" *)
      key  = $sample_Key;
       keyo = Some key;
      b' = A.guess(keyo);
     }
    }
    b = ${0,1};
    return (b = b');
  }
}.


(* specs about eqS, find_id, find_str, find_matching *)

lemma cmatching_id : forall s,
cmatching (cmatching s) = s.
proof strict.
 intros => s.
 by rewrite /cmatching; elim /tuple5_ind s => A B X Y r; rewrite /cmatching /=.
save.

local lemma find_matching_spec_ll :
forall id' id_set',
bd_hoare [AKE_find(A).O.find_matching : 
id' = id /\ id_set' = id_set /\
in_dom id AKE_find.mCompleted /\
in_dom id AKE_find.mStarted /\
in_dom id AKE_find.mEexp /\ 
(forall j, mem j id_set => 
     in_dom id AKE_find.mCompleted /\
    in_dom id AKE_find.mStarted /\
    in_dom id AKE_find.mEexp ) ==>
(res = None => 
(forall j, mem j id_set' =>
( cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j) <>
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id') /\
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j <>
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id')))) /\
(res <> None => mem (proj res) id_set' /\
 (((cmatching  
  (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj res))) =
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id') \/
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj res) =
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id'))))] = 1%r.
proof strict.
 intros => id' id_set'; fun.
 sp.
 while 
(sid = compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id /\
 (ret = None => (forall j, mem j id_set /\ ! mem j aux => 
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j <>
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id) /\
(cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j)) <>
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id))) /\
 (forall j, mem j aux => mem j id_set) /\
 (ret <> None =>  mem (proj ret) id_set /\
 ((compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj ret) =
 cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id)) \/
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj ret) =
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id))))) 
(card aux).
intros =>z; wp; skip; progress => //.
 smt.
 smt.
 by generalize H4; rewrite mem_rm => [h1 h2]; apply H0.
 rewrite !proj_some; first by apply H0; apply mem_pick.
 rewrite !proj_some; generalize H3 => [|] <- //.
 by rewrite cmatching_id.
 by apply mem_rm_variant.
 generalize H5; rewrite mem_rm not_and => [|] h.
  cut := H _ j0 _ => //.
  rewrite (_ : j0 = pick aux{hr}); first smt.
  generalize H3; rewrite not_or => [h1 h2]; smt.
 generalize H5; rewrite mem_rm not_and => [|] h.
  cut := H _ j0 _ => //.
  rewrite (_ : j0 = pick aux{hr}); first smt.
  generalize H3; rewrite not_or => [h1 h2]; smt.
 by apply H0; generalize H4; rewrite mem_rm.
 by apply mem_rm_variant.

skip; progress => //.
 smt.
 smt.
 rewrite not_and; left.
 by rewrite card_le_0.
 cut := H4 _ j0 _ => //; split => //.
 generalize H3; rewrite not_and => [] //.
  rewrite (_ : forall (p : bool), (!(! p)) = p); first smt.
  by intros => ->; smt.
 cut := H4 _ j0 _ => //; split => //.
 generalize H3; rewrite not_and => [] //.
  rewrite (_ : forall (p : bool), (!(! p)) = p); first smt.
  by intros => ->; smt.
 cut := H6 _ => //.
 cut := H6 _ => //.
 by intros => [h1 [|]] ->; [left | right]; rewrite ?cmatching_id.
save.

local lemma find_matching_spec :
forall id' id_set',
hoare [AKE_find(A).O.find_matching : 
id' = id /\ id_set' = id_set /\
in_dom id AKE_find.mCompleted /\
in_dom id AKE_find.mStarted /\
in_dom id AKE_find.mEexp /\ 
(forall j, mem j id_set => 
     in_dom id AKE_find.mCompleted /\
    in_dom id AKE_find.mStarted /\
    in_dom id AKE_find.mEexp ) ==>
(res = None => 
(forall j, mem j id_set' =>
( cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j) <>
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id') /\
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j <>
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id')))) /\
(res <> None => mem (proj res) id_set' /\
 (((cmatching  
  (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj res))) =
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id') \/
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj res) =
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id'))))].
proof strict.
 intros => id' id_set'; fun.
 sp.
 while 
(sid = compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id /\
 (ret = None => (forall j, mem j id_set /\ ! mem j aux => 
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j <>
 compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id) /\
(cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted j)) <>
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id))) /\
 (forall j, mem j aux => mem j id_set) /\
 (ret <> None =>  mem (proj ret) id_set /\
 ((compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj ret) =
 cmatching (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id)) \/
(compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted (proj ret) =
 (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id))))).
 wp; skip; progress => //.
 smt.
 smt.
 by apply H0;  generalize H4; rewrite mem_rm.
 by rewrite proj_some; apply H0; apply mem_pick.
 rewrite !proj_some;generalize H3 => [|] <- //.
 by rewrite cmatching_id.
 generalize H5; rewrite mem_rm not_and => [|] h.
  cut := H _ j0 _ => //.
  rewrite (_ : j0 = pick aux{hr}); first smt.
  generalize H3; rewrite not_or => [h1 h2]; smt.
 generalize H5; rewrite mem_rm not_and => [|] h.
  cut := H _ j0 _ => //.
  rewrite (_ : j0 = pick aux{hr}); first smt.
  generalize H3; rewrite not_or => [h1 h2]; smt.
 by apply H0; generalize H4; rewrite mem_rm.
skip; progress => //.
 smt.
 smt.
 cut := H4 _ j0 _ => //; split => //.
 generalize H3; rewrite not_and => [] //.
  rewrite (_ : forall (p : bool), (!(! p)) = p); first smt.
  by intros => ->; smt.
 cut := H4 _ j0 _ => //; split => //.
 generalize H3; rewrite not_and => [] //.
  rewrite (_ : forall (p : bool), (!(! p)) = p); first smt.
  by intros => ->; smt.
 cut := H6 _ => //.
 cut := H6 _ => //.
 by intros => [_ [|]] ->; [left | right]; rewrite ?cmatching_id.
save.

local lemma eqS_spec_ll : 
forall str sid, 
bd_hoare [AKE_find(A).O.eqS : 
i = sid /\ str =ss  /\ 
in_dom i AKE_find.mCompleted /\  
in_dom i AKE_find.mStarted /\ 
in_dom i AKE_find.mEexp ==>
res <> None /\
proj (res) =
(get_string_from_id sid AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = str)] = 1%r.
proof strict.
  intros => str sid; fun.  
   wp; skip; progress => //.
 smt.
 rewrite proj_some /get_string_from_id.
 elim /tuple3_ind (proj AKE_find.mStarted{hr}.[i{hr}]) => /= A B r heq.
 by rewrite /sd2_role/sd2_actor/sd2_peer /=.
save.

local lemma eqS_spec : 
forall str sid, 
hoare [AKE_find(A).O.eqS : 
i = sid /\ str =ss  /\ 
in_dom i AKE_find.mCompleted /\  
in_dom i AKE_find.mStarted /\ 
in_dom i AKE_find.mEexp ==>
res <> None /\
proj (res) =
(get_string_from_id sid AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = str)].
proof strict.
  intros => str sid; fun.
   wp; skip; progress => //.
 smt.
 rewrite proj_some /get_string_from_id.
 elim /tuple3_ind (proj AKE_find.mStarted{hr}.[i{hr}]) => /= A B r heq.
 by rewrite /sd2_role/sd2_actor/sd2_peer /=.
save.


local lemma  find_id_spec :  
forall v sid, 
hoare [AKE_find(A).O.find_id : 
v = sstr /\ sid = s  /\
(forall i, mem i s => in_dom i AKE_find.mCompleted /\ 
                      in_dom i AKE_find.mStarted /\ 
                      in_dom i AKE_find.mEexp) ==> 
(res <> None => 
get_string_from_id (proj res) AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = v /\ mem (proj res) sid) /\
(res = None => 
 (forall id, mem id sid => 
get_string_from_id id AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> v))].
proof strict.
 intros => v sid; fun.
 while ((ret = None => 
 (forall id, mem id sid  => !mem id aux => get_string_from_id id AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> v)) /\
(forall i, mem i aux => mem i s) /\
(forall i, mem i aux => in_dom i AKE_find.mCompleted /\ 
                      in_dom i AKE_find.mStarted /\ 
                      in_dom i AKE_find.mEexp) /\ v = sstr /\
(ret <> None => 
get_string_from_id (proj ret) AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = v /\ mem (proj ret) s)).
 wp.
 sp.
 exists* i;elim* => i'.
 exists* sstr; elim* => sstr'.
 call (eqS_spec sstr' i').
 skip; progress => //.
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  generalize H11; rewrite mem_rm not_and => [|] h.
   by apply H.
   generalize H9; case (! result = None && proj result); first by smt.
   intros => h'; cut : !proj result by smt => {h'}  h' h'' {h''}.
   cut -> : id = pick auxR by smt => {h}.   
   by generalize h'; rewrite H8.   
 
   by generalize H9; rewrite mem_rm => [h1 h2]; apply H0.  

  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].
  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].
  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].

  case (! result = None && proj result); last by smt. 
   by rewrite H8 proj_some; intros => {H9} [] h1 ->.

  case (! result = None && proj result); last by smt. 
   by rewrite proj_some => _; apply H0; apply mem_pick.

 wp; skip; progress => //.
 smt.
 by cut := H1 _ id _ _; smt.
save.


local lemma  find_id_spec_ll :  
forall v sid, 
bd_hoare [AKE_find(A).O.find_id : 
v = sstr /\ sid = s  /\
(forall i, mem i s => in_dom i AKE_find.mCompleted /\ 
                      in_dom i AKE_find.mStarted /\ 
                      in_dom i AKE_find.mEexp) ==> 
(res <> None => 
get_string_from_id (proj res) AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = v /\ mem (proj res) sid) /\
(res = None => 
 (forall id, mem id sid => 
get_string_from_id id AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> v))] = 1%r.
proof strict.
 intros => v sid; fun.
 while ((ret = None => 
 (forall id, mem id sid  => !mem id aux => get_string_from_id id AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> v)) /\
(forall i, mem i aux => mem i s) /\
(forall i, mem i aux => in_dom i AKE_find.mCompleted /\ 
                      in_dom i AKE_find.mStarted /\ 
                      in_dom i AKE_find.mEexp) /\ v = sstr /\
(ret <> None => 
get_string_from_id (proj ret) AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = v /\ mem (proj ret) s)) (card aux).
 intros => z; wp; sp.
 exists* i;elim* => i'.
 exists* sstr; elim* => sstr'.
 call (eqS_spec_ll sstr' i').
 wp; skip; progress => //.
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  by elim (H1 (pick auxR) _); [by apply mem_pick | smt].
  generalize H11; rewrite mem_rm not_and => [|] h.
   by apply H.
   generalize H9; case (! result = None && proj result); first by smt.
   intros => h'; cut : !proj result by smt => {h'}  h' h'' {h''}.
   cut -> : id = pick auxR by smt => {h}.   
   by generalize h'; rewrite H8.   
 
   by generalize H9; rewrite mem_rm => [h1 h2]; apply H0.  

  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].
  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].
  by cut := H1 i0 _ => //;generalize H9; rewrite mem_rm => [].

  case (! result = None && proj result); last by smt. 
   by rewrite H8 proj_some; intros => {H9} [] h1 ->.

  case (! result = None && proj result); last by smt. 
   by rewrite proj_some => _; apply H0; apply mem_pick.
  
  by apply mem_rm_variant.

 wp; skip; progress => //.
 smt.
 smt.
 by cut := H1 _ id _; smt.
save.


local lemma  find_string_spec :  
forall i set_str, 
hoare [AKE_find(A).O.find_string : 
id = i /\ set_str = sstr  /\
in_dom id AKE_find.mCompleted /\ 
in_dom id AKE_find.mStarted /\ 
in_dom id AKE_find.mEexp ==> 
(res <> None => 
get_string_from_id i  AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = 
(proj res) /\ mem (proj res) set_str) /\
(res = None => 
 ! mem (get_string_from_id i AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) set_str )].
proof strict.
 intros => i set_str; fun.
 while 
((ret = None => 
 (forall s, mem s set_str => !mem s aux => 
 get_string_from_id id AKE_find.mStarted 
    AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> s)) /\
in_dom id AKE_find.mCompleted /\ 
in_dom id AKE_find.mStarted /\ 
in_dom id AKE_find.mEexp /\
(ret <> None => 
 get_string_from_id id AKE_find.mStarted 
    AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = proj ret /\ mem (proj ret) set_str) /\
 (forall s, mem s aux => mem s set_str)).
 sp.
 wp.
 exists* id;elim* => i'.
 exists* str; elim* => str'.
 call (eqS_spec str' i').
 skip; progress => //.
  generalize H13; rewrite mem_rm not_and => [hndom|heq].
   by apply H => //.

   cut ->: s = pick auxR by smt => {heq}.
   cut:! (! result = None && proj result) by smt => {H11} H11.
   cut: (! proj result) by smt => {H11}.
   by rewrite H10.

  case (! result = None && proj result); last by smt.
  intros => h.
  cut : proj result by smt => {h}. 
  by rewrite proj_some H10.

  case (! result = None && proj result); last by smt.
  rewrite proj_some => _.
  apply H4.
  by apply mem_pick.
  
  by generalize H11; rewrite mem_rm => [h] h'; apply H4.
 wp; skip; progress => //.
  smt.
  apply not_def => h.
  cut := H3 _ (get_string_from_id id{hr} AKE_find.mStarted{hr} AKE_find.mCompleted{hr}
       AKE_find.mEexp{hr} AKE_find.mSk{hr}) _  _ => //; smt.
save.

local lemma  find_string_spec_ll :  
forall i set_str, 
bd_hoare [AKE_find(A).O.find_string : 
id = i /\ set_str = sstr  /\
in_dom id AKE_find.mCompleted /\ 
in_dom id AKE_find.mStarted /\ 
in_dom id AKE_find.mEexp ==> 
(res <> None => 
get_string_from_id i  AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = 
(proj res) /\ mem (proj res) set_str) /\
(res = None => 
 ! mem (get_string_from_id i AKE_find.mStarted AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) set_str )] = 1%r.
proof strict.
 intros => i set_str; fun.
 while 
((ret = None => 
 (forall s, mem s set_str => !mem s aux => 
 get_string_from_id id AKE_find.mStarted 
    AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk <> s)) /\
in_dom id AKE_find.mCompleted /\ 
in_dom id AKE_find.mStarted /\ 
in_dom id AKE_find.mEexp /\
(ret <> None => 
 get_string_from_id id AKE_find.mStarted 
    AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk = proj ret /\ mem (proj ret) set_str) /\
 (forall s, mem s aux => mem s set_str))(card aux).
 intros => z.
 sp.
 wp.
 exists* id;elim* => i'.
 exists* str; elim* => str'.
 call (eqS_spec_ll str' i').
 skip; progress => //.
  generalize H13; rewrite mem_rm not_and => [hndom|heq].
   by apply H => //.

   cut ->: s = pick auxR by smt => {heq}.
   cut:! (! result = None && proj result) by smt => {H11} H11.
   cut: (! proj result) by smt => {H11}.
   by rewrite H10.

  case (! result = None && proj result); last by smt.
  intros => h.
  cut : proj result by smt => {h}. 
  by rewrite proj_some H10.

  case (! result = None && proj result); last by smt.
  rewrite proj_some => _.
  apply H4.
  by apply mem_pick.
  
  by generalize H11; rewrite mem_rm => [h] h'; apply H4.
  
  by apply mem_rm_variant.

 wp; skip; progress => //.
  smt.
  rewrite not_and; left.
  by rewrite card_le_0.
  apply not_def => h.
  cut := H3 _ (get_string_from_id id{hr} AKE_find.mStarted{hr} AKE_find.mCompleted{hr}
         AKE_find.mEexp{hr} AKE_find.mSk{hr})  _ _ => //; smt.
save.

pred is_dom (s : 'a set) (m : ('a,'b) map) = 
forall x, in_dom x m <=> FSet.mem x s.

lemma is_dom_add : forall m s (x : 'a) (v : 'b),
is_dom s m =>
is_dom (add x s) m.[x<-v].
proof strict.
 intros => m s x v.
 rewrite /is_dom => hdom y.
 case (y = x) => h.
  by rewrite h in_dom_setE mem_add; progress.

  rewrite in_dom_setNE // hdom mem_add; progress; first by left.
  by elim H;[ | smt]. 
save.


pred inv_split_dom (mH21 mH22 : (Sstring, Key) map) 
                   (mKeyRev2 : (Sidx, Key) map) 
                   mStarted2 mCompleted2 mEexp2 mSk2 = 
(forall x, in_dom x mH21 <=> 
  (in_dom x mH22 \/ 
  (exists i, in_dom i mKeyRev2 /\
 get_string_from_id i mStarted2
    mCompleted2 mEexp2 mSk2 = x))).

pred inv_split_val1 (mH21 mH22 : (Sstring, Key) map) =
forall x, in_dom x mH22 => mH22.[x] = mH21.[x].

pred inv_split_val2 (mH21 : (Sstring, Key) map) 
                   (mKeyRev2 : (Sidx, Key) map) 
                   mStarted2 mCompleted2 mEexp2 mSk2 = 
forall i, in_dom i mKeyRev2 => mKeyRev2.[i] = 
            mH21.[get_string_from_id i mStarted2 mCompleted2 mEexp2 mSk2].

lemma inv_split_dom_in_dom : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x,
in_dom x mH22 =>
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
in_dom x mH21.
proof strict.
 progress.
 cut [h1 h2] := H0 x => {h1}.
 by apply h2 => {h2}; left.
save.

lemma inv_split_dom_updmH22 : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_dom mH21.[x <- v] mH22.[x <- v] mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2.
proof strict.
 progress => str.
 case (str = x)=> h.
  by rewrite h !in_dom_setE.
  by rewrite !in_dom_setNE //; apply H.
save.

lemma inv_split_dom_updmKeyRev : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
!in_dom (get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2) mH21 =>
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_dom mH21.[get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2 <- v]
     mH22 mKeyRev2.[x <- v] mStarted2 mCompleted2 mEexp2 mSk2.
proof strict.
 progress => str.
 case (str = get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2) => h.
  rewrite h !in_dom_setE; progress => //.
   by right; exists x; rewrite in_dom_setE.

  rewrite !in_dom_setNE //; progress => //.
   generalize H1; rewrite H0 => [hdom | hex] ; [by left | right].
   elim hex => i [h1 h2] {hex}.
   case (i = x) => heq; first by (generalize H h1; rewrite heq; smt).
    exists i; rewrite in_dom_setNE //.
  generalize H1 => [hdom | [i] [h1 h2]].
   by rewrite H0; left.
   case (i = x) => heq; first by (generalize H h1; rewrite heq; smt).
   by rewrite H0; right; exists i; generalize h1; rewrite in_dom_setNE.
save.
     
lemma inv_split_dom_updmStarted : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom x mKeyRev2 => 
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_dom mH21 mH22 mKeyRev2 mStarted2.[x<-v] mCompleted2 mEexp2 mSk2.
proof strict.
 progress.
 generalize H0; rewrite  /inv_split_dom; progress. 
  generalize H1; rewrite H0 => [|] h.
   by left.
   right; elim h => {h} i [h1 h2].
   exists i; rewrite -get_string_pres => //.  
    by apply not_def => h; generalize h1; rewrite -h.
  generalize H1; rewrite H0 => [|] h. 
   by left.
   right; elim h => {h} i [h1].
   rewrite -get_string_pres => //. 
    by apply not_def => h; generalize h1; rewrite -h.
    intros heq; exists i.
    by rewrite heq.
save.  
 
lemma inv_split_dom_updmCompleted : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom x mKeyRev2 => 
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2.[x<-v] mEexp2 mSk2.
proof strict.
 progress.
 generalize H0; rewrite  /inv_split_dom; progress. 
  generalize H1; rewrite H0 => [|] h.
   by left.
   right; elim h => {h} i [h1 h2].
   exists i; rewrite -get_string_pres2 => //.  
    by apply not_def => h; generalize h1; rewrite -h.
  generalize H1; rewrite H0 => [|] h. 
   by left.
   right; elim h => {h} i [h1].
   rewrite -get_string_pres2 => //. 
    by apply not_def => h; generalize h1; rewrite -h.
    intros heq; exists i.
    by rewrite heq.
save.  

lemma inv_split_val1_updmH22 : 
forall (mH21 mH22 : (Sstring, Key) map) x v,
inv_split_val1 mH21 mH22  =>
inv_split_val1 mH21.[x <- v] mH22.[x <- v].
proof strict.
 progress => str.
 case (str = x)=> h.
  by rewrite h !get_setE.
  rewrite !get_setNE ?in_dom_setNE //; first 2 smt.
  by intros => hdom; rewrite H.
save.

lemma inv_split_val1_updmKeyRev : 
forall (mH21 mH22 : (Sstring, Key) map) x v,
!in_dom x mH22 => 
inv_split_val1 mH21 mH22  =>
inv_split_val1 mH21.[x <- v] mH22.
proof strict.
 progress => str.
 case (str = x)=> h.
  by generalize H; rewrite h; smt.
  rewrite !get_setNE ?in_dom_setNE //; first smt.
  by intros => hdom; rewrite H0.
save.


lemma inv_split_val2_updmH22 : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom x mH21 => 
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21.[x <- v] mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2.
proof strict.
 progress => id hdom.
 rewrite get_setNE; last first.
  by apply H1.
 apply not_def => heq.
 generalize H; rewrite H0 not_or => [h]{h}h.
 cut : exists (i : Sidx),
         in_dom i mKeyRev2 /\
         get_string_from_id i mStarted2 mCompleted2 mEexp2 mSk2 = x; last by smt.
 by exists id; split => //; rewrite heq.
save.

lemma inv_split_val2_updmKeyRev : 
forall (mH21 mH22 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom (get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2) mH21 => 
inv_split_dom mH21 mH22 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21.[(get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2) <- v] 
mKeyRev2.[x <- v] mStarted2 mCompleted2 mEexp2 mSk2.
proof strict.
 progress => i hdom.
 case (x = i) => heq.
  by rewrite heq !get_setE.
  generalize hdom; rewrite get_setNE //.

  rewrite in_dom_set =>[|]; last smt.
  intros => hdom; generalize H; rewrite H0 not_or => [h1 h2].
  case (get_string_from_id x mStarted2 mCompleted2 mEexp2 mSk2 =
        get_string_from_id i mStarted2 mCompleted2 mEexp2 mSk2); last first.
  intros => hneq.
  by rewrite get_setNE // H1.
  intros => heq'.
  cut: false; last smt.
  generalize hdom => /=.
  generalize h2.
  cut h: forall p q, (p => q) => ! q => ! p by smt.
  apply h => hdom.
  by exists i; progress => //; rewrite heq'.
save.

lemma inv_split_val2_updmStarted : 
forall (mH21 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom x mKeyRev2 => 
inv_split_val2 mH21 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21 mKeyRev2 mStarted2.[x <- v] mCompleted2 mEexp2 mSk2.
proof strict.
 progress.
 generalize H0; rewrite /inv_split_val2.
 progress.
 rewrite H0 => //.
 rewrite -get_string_pres => //.
 by apply not_def => h; generalize H; rewrite h.
save.

lemma inv_split_val2_updmCompleted : 
forall (mH21 : (Sstring, Key) map) 
               (mKeyRev2 : (Sidx, Key) map) 
                 mStarted2 mCompleted2 mEexp2 mSk2 x v,
! in_dom x mKeyRev2 => 
inv_split_val2 mH21 mKeyRev2 mStarted2 mCompleted2 mEexp2 mSk2 =>
inv_split_val2 mH21 mKeyRev2 mStarted2 mCompleted2.[x <- v] mEexp2 mSk2.
proof strict.
 progress.
 generalize H0; rewrite /inv_split_val2.
 progress.
 rewrite H0 => //.
 rewrite -get_string_pres2 => //.
 by apply not_def => h; generalize H; rewrite h.
save.

 
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

pred actor_valid mStrt mCmp mEexp (mSk : (Agent, Sk) map) =
forall (i : Sidx), in_dom i mStrt =>
       in_dom (sid_actor (compute_sid mStrt mEexp  mCmp i)) mSk. 

pred mSk_inv (mSk : (Agent, Sk) map) =   
forall (s : Pk),  in_dom s mSk =>gen_pk (proj mSk.[s]) = s.

pred univ_map  (m : ('a, 'b) map) =
 forall x, in_dom x m.

local equiv AKE_RandCompute_Eqs_h2 : 
AKE_ComputeRand(A).O.h2 ~ AKE_find(A).O.h2 :
  ={sstring} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}
 ==>
  ={res} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 fun.
 sp.
 seq 1 1:
  (  s{2} = None /\
  ={sstring,ke}  /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}).
 by rnd.
 if{1}.
 rcondf{2} 1.
 intros => &m; wp; skip; progress => //.
  by generalize H9; rewrite  H1 not_or => [].
  rcondf{2} 2.
  intros => &m.
  exists* sstring; elim* => str.
  exists* AKE_find.sKeyRev; elim* => id_set. 
  call (find_id_spec str id_set).
   wp; skip; progress => //.
   by apply H5; rewrite H0.
   by apply H4; apply H5; rewrite H0.
   by apply H6.
   case (result = None) => // habs.
   cut := H11 _ => //.
   intros => [h1 h2].
   cut: in_dom sstring{hr} AKE_ComputeRand.mH2{m}; last by smt.
    rewrite H1; right.
    by exists (proj result); split; rewrite ?H0.

 wp.
 exists* sstring{2}; elim* => str.
 exists* AKE_find.sKeyRev{2}; elim* => id_set. 
 call{2} (find_id_spec_ll str id_set).
 skip; progress => //.
   by apply H5; rewrite H0.
   by apply H4; apply H5; rewrite H0.
   by apply H6.
   by rewrite !get_setE proj_some.
   by apply is_dom_add.
   by apply inv_split_dom_updmH22.
   by apply inv_split_val1_updmH22.
   by apply (inv_split_val2_updmH22 _ AKE_find.mH2{2}).
  
 if{2}.
 wp; skip; progress => //.
  by rewrite H2.
 rcondt{2} 2.
 intros => &m.
 exists* sstring; elim* => str.
 exists* AKE_find.sKeyRev; elim* => id_set. 
 call{2} (find_id_spec str id_set).
 wp; skip; progress => //.
   by apply H5; rewrite H0.
   by apply H4; apply H5; rewrite H0.
   by apply H6.
   apply not_def => h.
   generalize H9; rewrite H1 =>[|]; [smt|].
    by intros => [i][hi1] /=; apply H13 => //; rewrite -H0.
  
 wp.
 exists* sstring{2}; elim* => str.
 exists* AKE_find.sKeyRev{2}; elim* => id_set. 
 call{2} (find_id_spec_ll str id_set).
 skip; progress => //.  
   by apply H5; rewrite H0.
   by apply H4; apply H5; rewrite H0.
   by apply H6.
   cut [heq hmem]:= H12 _ => //.
   apply not_def => h.
   generalize H9; rewrite H1 =>[|]; [smt|].
   by intros => [i][hi1] /=; apply H13 => //; rewrite -H0.

   rewrite H3 => //.
   by rewrite H0.
   by rewrite heq.
save.

local equiv AKE_RandCompute_Eqs_h2a : 
AKE_ComputeRand(A).O.h2_a ~ AKE_find(A).O.h2_a :
  ={sstring} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2} 
 ==>
  ={res} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 by fun; sp; if => //; wp; call AKE_RandCompute_Eqs_h2; wp.
qed.
   

lemma some_proj : forall (x : 'a option),
x <> None =>
Some (proj x) = x.
proof strict.
 intros => x hnn.
 elim /option_case_eq x; first smt.
  intros => [y] ->.
  by rewrite proj_some.
save.

lemma some_get : 
forall (m : ('a, 'b) map) (x : 'a),
in_dom x m =>
Some (proj m.[x]) = m.[x].
proof strict.
 intros => m x hdom.
 apply some_proj.
 by generalize hdom; rewrite /in_dom.
save.

lemma tuple_eq : 
forall (A1 A2 : 'a) (B1 B2 : 'b) (X1 X2 : 'c)(Y1 Y2 : 'd)(r1 r2 : 'e),
((A2, B2, X2, Y2, r2) =
 (A1, B1, X1, Y1, r1)) <=>
 A1 = A2 /\ B1 = B2 /\ X1 = X2 /\ Y1 = Y2 /\ r1 = r2.
proof strict.
 progress.
save.

lemma partnering_correct :
forall i j mStrt mCmp mEexp mSk,
(forall s, in_dom s mSk => gen_pk(proj mSk.[s]) =  s) =>
in_dom (sid_actor (compute_sid mStrt mEexp mCmp i)) mSk =>
in_dom (sid_actor (compute_sid mStrt mEexp mCmp j)) mSk =>
compute_sid mStrt mEexp mCmp i =
compute_sid mStrt mEexp mCmp j \/
compute_sid mStrt mEexp mCmp i =
cmatching (compute_sid mStrt mEexp mCmp j) =>
get_string_from_id i mStrt mCmp mEexp mSk =
get_string_from_id j mStrt mCmp mEexp mSk.
proof strict.
 progress => //.
 generalize H0 H1.
 elim H2 => {H2};
 rewrite /compute_sid /get_string_from_id /cmatching /sid_actor;
 elim /tuple3_ind (proj mStrt.[i]);
 elim /tuple3_ind (proj mStrt.[j]) => /= A1 B1 r1 heq1 A2 B2 r2 heq2.
 rewrite tuple_eq.
 progress.
 cut -> : proj mEexp.[i] = proj mEexp.[j].
  by apply gen_epk_inj; rewrite H0.
 by rewrite H1.
rewrite strong_partnering.
 rewrite tuple_eq; progress; right; progress.
 by rewrite H.
 by rewrite H.
 by rewrite -H1.
 smt.
save.
 
local equiv AKE_RandCompute_Eqs_computeKey : 
AKE_ComputeRand(A).O.computeKey ~ AKE_find(A).O.computeKey :
  ={i} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}  
 ==>
  ={res} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 conseq (_ : _ ==> 
 (AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}) && ={res}).
  by progress => //.
 fun; sp; if => //.
 inline AKE_ComputeRand(A).O.h2.
seq 3 1:
   ( sstring{1} =
  gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{1}])
    (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
    (proj AKE_ComputeRand.mCompleted{1}.[i{1}]) ro{1} /\
  ((a{1}, b{1}, ro{1}) = proj AKE_ComputeRand.mStarted{1}.[i{1}] /\
   str{2} = None /\
   ret{2} = None /\
   r{2} = None /\
   r{1} = None /\
   ke{1} = k{2} /\
   ={i} /\
   AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
   AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
   AKE_find.test{2} = AKE_ComputeRand.test{1} /\
   AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
   AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
   AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
   AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
   AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
   AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
   AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
   is_dom AKE_find.sH2'{2} AKE_find.mH2{2} /\
   is_dom AKE_find.sKeyRev{2} AKE_find.mKeyRev{2} /\
   inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2}
     AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
     AKE_find.mSk{2} /\
   inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
   inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2}
     AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
     AKE_find.mSk{2} /\
   is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
   is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\
   univ_map AKE_find.mEexp{2}) /\
  in_dom i{1} AKE_ComputeRand.mCompleted{1} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}).
  by wp; rnd; wp.
  if{1}.
  rcondf{2} 1.
   intros => &m; skip; progress => //.  
   generalize H11; rewrite H2 not_or => [h1] {h1}.
   cut h : forall a b, (a => b ) => (!b => !a) by smt.
   apply h.
   intros => hdom; exists i{hr}; progress => //.
   by rewrite /get_string_from_id -H /=.
 
  rcondf{2} 2.
   intros => &m.
   exists* i; elim* => i'.
   exists* AKE_find.sKeyRev; elim* => sid_set'.
   call (find_matching_spec i' sid_set'); skip; progress => //.
    by apply H5. 
    by apply H7.
    by apply H5.
    by apply H7.
    generalize H16 H17; case (result = None) => // hres h1 h2.   
    cut  := h2 _ => // {h1}{h2}.
    intros => [] h h'.
    generalize H11 => /=.
    rewrite H2.
    right.
    exists (proj result); split.
     by rewrite H1.
  cut :
  gen_sstring (proj AKE_ComputeRand.mEexp{m}.[i{hr}])
  (proj AKE_ComputeRand.mSk{m}.[a{m}]) b{m}
  (proj AKE_ComputeRand.mCompleted{m}.[i{hr}]) ro{m} =
  get_string_from_id i{hr} AKE_ComputeRand.mStarted{m}
  AKE_ComputeRand.mCompleted{m} AKE_ComputeRand.mEexp{m}
  AKE_ComputeRand.mSk{m}.
  by rewrite /get_string_from_id -H.
  intros => ->.
  apply partnering_correct. 
  by progress; apply H10.
  by apply H9; apply H5; apply H6; rewrite H1.
  by apply H9.
  elim h' => <- //.
  by rewrite cmatching_id.
 
   rcondf{2} 3.
 intros => &m.
 exists* i; elim* => i'.
 exists* AKE_find.sH2'; elim* => str_set'.
 exists* AKE_find.sKeyRev; elim* => sid_set'.
 call (find_string_spec i' str_set').
 call (find_matching_spec i' sid_set').
 skip; progress => //.
   by apply H5. 
   by apply H7.
   by apply H5. 
   by apply H7.
   case (result0 = None) => //.
   intros => h.
   cut:=  H21 _ => // {H21} {H22}. 
   intros => [<- hmem].
   generalize H11 => /=.
   rewrite H2; left.
   rewrite H0.
   generalize hmem.
   by rewrite /get_string_from_id -H.
  
  wp.
  exists* i{2}; elim* => i'.
  exists* AKE_find.sH2'{2}; elim* => str_set.
  exists* AKE_find.sKeyRev{2}; elim* => sid_set'.
  call{2} (find_string_spec_ll i' str_set);
  call{2} (find_matching_spec_ll i' sid_set'); wp; skip; progress => //.
   by apply H5. 
   by apply H7.
   by apply H5. 
   by apply H7.
   by apply is_dom_add.
   rewrite (_:  gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{2}])
                            (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
                            (proj AKE_ComputeRand.mCompleted{1}.[i{2}]) ro{1} =
                get_string_from_id i{2} AKE_ComputeRand.mStarted{1} 
                                        AKE_ComputeRand.mCompleted{1}  
                                        AKE_ComputeRand.mEexp{1}
                                        AKE_ComputeRand.mSk{1}).
    by rewrite /get_string_from_id -H.
   apply inv_split_dom_updmKeyRev => //. 
    by rewrite /get_string_from_id -H.
   
   apply inv_split_val1_updmKeyRev => //.
   generalize H11; apply (_ : forall p q, (p => q) => (!q => !p)); first smt.
    by rewrite H2 => _; left.

   rewrite (_ : gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{2}])
                            (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
                            (proj AKE_ComputeRand.mCompleted{1}.[i{2}]) ro{1} =
                get_string_from_id i{2} AKE_ComputeRand.mStarted{1}
                         AKE_ComputeRand.mCompleted{1} AKE_ComputeRand.mEexp{1}
                         AKE_ComputeRand.mSk{1}).
    by rewrite /get_string_from_id -H.
   apply (inv_split_val2_updmKeyRev _ AKE_find.mH2{2}) => //.
    generalize H11; apply (_ : forall p q, (p => q) => (!q => !p)); first smt.
    by rewrite /get_string_from_id -H.    
      
   by apply is_sub_map_upd3.
   by rewrite some_get ?in_dom_setE // get_setE.  
  if{2}.
   wp; skip; progress => //.
    rewrite some_get.
     rewrite H2; right; exists i{2}; progress => //.
     by rewrite /get_string_from_id -H.
     by rewrite H17 // /get_string_from_id -H.
seq 0 1:
(((sstring{1} =
    gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{1}])
      (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
      (proj AKE_ComputeRand.mCompleted{1}.[i{1}]) ro{1} /\
    ((a{1}, b{1}, ro{1}) = proj AKE_ComputeRand.mStarted{1}.[i{1}] /\
     str{2} = None /\
     ret{2} = None /\
     r{2} = None /\
     r{1} = None /\
     ke{1} = k{2} /\
     ={i} /\
     AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
     AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
     AKE_find.test{2} = AKE_ComputeRand.test{1} /\
     AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
     AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
     AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
     AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
     AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
     AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
     AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
     is_dom AKE_find.sH2'{2} AKE_find.mH2{2} /\
     is_dom AKE_find.sKeyRev{2} AKE_find.mKeyRev{2} /\
     inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2}
       AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
       AKE_find.mSk{2} /\
     inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
     inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2}
       AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
       AKE_find.mSk{2} /\
     is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
     is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\
     univ_map AKE_find.mEexp{2}) /\
    in_dom i{1} AKE_ComputeRand.mCompleted{1} /\
    actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
      AKE_find.mSk{2} /\
    mSk_inv AKE_find.mSk{2}) /\
   ! ! in_dom sstring{1} AKE_ComputeRand.mH2{1}) /\
  ! in_dom i{2} AKE_find.mKeyRev{2} /\
(j{2} = None => 
 forall (j : Sidx),
       mem j AKE_find.sKeyRev{2} =>
       ! cmatching
           (compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
              AKE_ComputeRand.mCompleted{1} j) =
         compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
           AKE_ComputeRand.mCompleted{1} i{2} /\
       ! compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
           AKE_ComputeRand.mCompleted{1} j =
         compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
           AKE_ComputeRand.mCompleted{1} i{2} ) /\
(j{2}  <> None =>
     mem (proj  j{2}) AKE_find.sKeyRev{2} /\
     (cmatching
        (compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
           AKE_ComputeRand.mCompleted{1} (proj j{2})) =
      compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
        AKE_ComputeRand.mCompleted{1} i{2} \/
      compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
        AKE_ComputeRand.mCompleted{1} (proj j{2}) =
      compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
        AKE_ComputeRand.mCompleted{1} i{2}))).
   exists* i{2}; elim* => i'.
   exists* AKE_find.sKeyRev{2}; elim* => sid_set.
   call{2} (find_matching_spec_ll i' sid_set); skip; progress => //.
    by apply H5. 
    by apply H7.
    by apply H5. 
    by apply H7.
    if{2}.
 wp; skip; progress => //.
 rewrite some_get => //.    
 rewrite H20.
 rewrite H17; cut := H14 _ => //.
 cut: gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{2}])
                          (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
                          (proj AKE_ComputeRand.mCompleted{1}.[i{2}]) ro{1} =
      get_string_from_id (proj j{2})
                          AKE_ComputeRand.mStarted{1}
                          AKE_ComputeRand.mCompleted{1}
                          AKE_ComputeRand.mEexp{1} AKE_ComputeRand.mSk{1}; last smt.
 cut ->: gen_sstring (proj AKE_ComputeRand.mEexp{1}.[i{2}])
  (proj AKE_ComputeRand.mSk{1}.[a{1}]) b{1}
  (proj AKE_ComputeRand.mCompleted{1}.[i{2}]) ro{1} =
  get_string_from_id i{2} AKE_ComputeRand.mStarted{1}
  AKE_ComputeRand.mCompleted{1} AKE_ComputeRand.mEexp{1}
  AKE_ComputeRand.mSk{1}.
  by rewrite /get_string_from_id -H.
  apply partnering_correct.
   by apply H25.
   by apply H24; apply H21.
   by apply H24; apply H21; apply H22; rewrite H17; cut := H14 _ => //.
   by cut [hmem [|] <-]:= H14 _ => //.
   
  rcondt{2} 2.
   intros => &m; wp.     
   exists* i; elim* => i'.
   exists* AKE_find.sH2'; elim* => str_set.
   call (find_string_spec i' str_set); skip; progress => //.
    by apply H5. 
    by apply H7.
    apply not_def => h'.
    generalize H11 => /=.
    rewrite H2; rewrite not_or; split.
    rewrite H0.
    cut := H19 _ => //.
    by rewrite /get_string_from_id -H /=.
    apply not_def => [[j]][hdom] heq.
    cut := H13 _ j _ => //=.
     by rewrite -H1.
    rewrite not_and /=. 
    cut: 
compute_sid AKE_ComputeRand.mStarted{m} AKE_ComputeRand.mEexp{m}
  AKE_ComputeRand.mCompleted{m} j =
compute_sid AKE_ComputeRand.mStarted{m} AKE_ComputeRand.mEexp{m}
  AKE_ComputeRand.mCompleted{m} i{hr} \/
compute_sid AKE_ComputeRand.mStarted{m} AKE_ComputeRand.mEexp{m}
     AKE_ComputeRand.mCompleted{m} j =
cmatching
(compute_sid AKE_ComputeRand.mStarted{m} AKE_ComputeRand.mEexp{m}
  AKE_ComputeRand.mCompleted{m} i{hr}).
 apply (strong_partnering_id _ _ _ _ _  AKE_ComputeRand.mSk{m}) => //.
 by apply H9; apply H5; apply H6.                           
 by apply H9.       
 by rewrite heq /get_string_from_id -H.
 intros => [|] -> //.
 by rewrite cmatching_id.
 wp.
 exists* i{2}; elim* => i'.
 exists* AKE_find.sH2'{2}; elim* => str_set.
 call{2} (find_string_spec_ll i' str_set); skip; progress => //.
  by apply H5.
  by apply H7.
  rewrite some_get => //.
  elim (H18  _); last first.
   intros => h1 h2. 
   rewrite H3.
   by rewrite H0.
   by rewrite -h1 /get_string_from_id -H /=.
    apply not_def => h'.
    generalize H11 => /=.
    rewrite H2; rewrite not_or; split.
    rewrite H0.
    cut := H19 _ => //.
    by rewrite /get_string_from_id -H /=.
    apply not_def => [[j]][hdom] heq.
    cut := H13 _ j _ => //=.
     by rewrite -H1.
    rewrite not_and /=. 
cut:  
 compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
   AKE_ComputeRand.mCompleted{1} j =
 compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
   AKE_ComputeRand.mCompleted{1} i{2} \/
 compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
   AKE_ComputeRand.mCompleted{1} j =
 cmatching
   (compute_sid AKE_ComputeRand.mStarted{1} AKE_ComputeRand.mEexp{1}
      AKE_ComputeRand.mCompleted{1} i{2}) .
apply (strong_partnering_id _ _ _ _ _  AKE_ComputeRand.mSk{1}).
 by apply H10.
 by apply H9; apply H5; apply H6.                           
 by apply H9.       
 by rewrite heq /get_string_from_id -H.
 intros => [|] -> //.
 by rewrite cmatching_id.
save.

local equiv AKE_RandCompute_Eqs_sessionRev : 
AKE_ComputeRand(A).O.sessionRev ~ AKE_find(A).O.sessionRev :
  ={i} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}  
 ==>
  ={res} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 by fun; sp; if => //; call AKE_RandCompute_Eqs_computeKey; wp; skip; progress.
save.
 

local equiv AKE_RandCompute_Eqs_choose : 
AKE_ComputeRand(A).A.choose ~ AKE_find(A).A.choose :
  ={s, glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}  
 ==>
  ={res, glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 fun (AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}) => //.
  by fun; wp.
  fun; wp; skip; progress; try assumption.
   apply inv_split_dom_updmStarted => //.
    apply not_def => h; generalize H11 => /=.
    by apply H4; apply H5.      

   apply inv_split_val2_updmStarted => //.   
    apply not_def => h; generalize H11 => /=.
    by apply H4; apply H5. 
     
   by apply is_sub_map_upd1.

   rewrite /actor_valid => j hdom; case (i{2} = j) => h.
   rewrite h.
    by rewrite /compute_sid get_setE proj_some /sid_actor /=.
    rewrite /compute_sid get_setNE //.
    generalize hdom; rewrite in_dom_setNE; first smt.
    intros => h''.
    by cut:= H7 j _.

  fun; wp; skip; progress; try assumption.
   apply inv_split_dom_updmCompleted => //.
    apply not_def => h; generalize H9 => /=.
    by apply H5.      

   apply inv_split_val2_updmCompleted => //.
    apply not_def => h; generalize H9 => /=.
    by apply H5.     
   by apply is_sub_map_upd3. 
   by apply is_sub_map_upd1. 

   rewrite /actor_valid => i hdom.
    cut:= H7 i _ => //.
    rewrite /compute_sid /sid_actor.
    by elim /tuple3_ind (proj AKE_ComputeRand.mStarted{1}.[i]) => /=.

  fun; wp; skip; progress; try assumption.
    apply inv_split_dom_updmCompleted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
    apply inv_split_dom_updmStarted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
   apply inv_split_val2_updmCompleted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
   apply inv_split_val2_updmStarted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     

   by apply is_sub_map_upd2. 
   by apply is_sub_map_upd1. 
   rewrite /actor_valid => j hdom; case (i{2} = j) => h.
   rewrite h.
    by rewrite /compute_sid get_setE proj_some /sid_actor /=.
    rewrite /compute_sid !get_setNE //.
    generalize hdom; rewrite in_dom_setNE; first smt.
    intros => h''.
    by cut:= H7 j _.
  fun; wp; skip; progress; try assumption.
  by apply AKE_RandCompute_Eqs_h2a.
  by apply AKE_RandCompute_Eqs_sessionRev.
save.


local equiv AKE_RandCompute_Eqs_guess : 
AKE_ComputeRand(A).A.guess ~ AKE_find(A).A.guess :
  ={k, glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}  
 ==>
  ={res, glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}.
proof strict.
 fun (AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2}) => //.
  by fun; wp.
  apply AKE_RandCompute_Eqs_h2a.
  fun; wp; skip; progress; try assumption.
   apply inv_split_dom_updmStarted => //.
    apply not_def => h; generalize H11 => /=.
    by apply H4; apply H5.      

   apply inv_split_val2_updmStarted => //.   
    apply not_def => h; generalize H11 => /=.
    by apply H4; apply H5. 
     
   by apply is_sub_map_upd1.

   rewrite /actor_valid => j hdom; case (i{2} = j) => h.
   rewrite h.
    by rewrite /compute_sid get_setE proj_some /sid_actor /=.
    rewrite /compute_sid get_setNE //.
    generalize hdom; rewrite in_dom_setNE; first smt.
    intros => h''.
    by cut:= H7 j _.

  fun; wp; skip; progress; try assumption.
   apply inv_split_dom_updmCompleted => //.
    apply not_def => h; generalize H9 => /=.
    by apply H5.      

   apply inv_split_val2_updmCompleted => //.
    apply not_def => h; generalize H9 => /=.
    by apply H5.     
   by apply is_sub_map_upd3. 
   by apply is_sub_map_upd1. 

   rewrite /actor_valid => i hdom.
    cut:= H7 i _ => //.
    rewrite /compute_sid /sid_actor.
    by elim /tuple3_ind (proj AKE_ComputeRand.mStarted{1}.[i]) => /=.

  fun; wp; skip; progress; try assumption.
    apply inv_split_dom_updmCompleted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
    apply inv_split_dom_updmStarted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
   apply inv_split_val2_updmCompleted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     
   apply inv_split_val2_updmStarted => //.
    apply not_def => h; generalize H12 => /=.
    by apply H5.     

   by apply is_sub_map_upd2. 
   by apply is_sub_map_upd1. 
   rewrite /actor_valid => j hdom; case (i{2} = j) => h.
   rewrite h.
    by rewrite /compute_sid get_setE proj_some /sid_actor /=.
    rewrite /compute_sid !get_setNE //.
    generalize hdom; rewrite in_dom_setNE; first smt.
    intros => h''.
    by cut:= H7 j _.
  fun; wp; skip; progress; try assumption.
  by apply AKE_RandCompute_Eqs_sessionRev.
save.


local equiv AKE_RandCompute_Eqs : 
AKE_ComputeRand(A).main ~ AKE_find(A).main :
={glob A} ==>
(AKE_ComputeRand.test <> None /\ 
in_dom AKE_ComputeRand.t_idx AKE_ComputeRand.mCompleted /\
mem
(get_string_from_id AKE_ComputeRand.t_idx AKE_ComputeRand.mStarted 
  AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp AKE_ComputeRand.mSk) 
AKE_ComputeRand.sH2 /\
fresh_op (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx) AKE_ComputeRand.evs){1} <=>
(AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\
mem
(get_string_from_id AKE_find.t_idx AKE_find.mStarted 
  AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) 
AKE_find.sH2 /\
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs){2}.
proof strict.
 fun.
  seq 14 17:
(={b,pks,key,keyo,b',i,pks, glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.mH2{2} = AKE_ComputeRand.mH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  AKE_find.mH2{2} = Map.empty /\
  AKE_find.sH2{2} = FSet.empty /\
  AKE_find.mCompleted{2} = Map.empty /\
  AKE_find.mStarted{2} = Map.empty /\
  AKE_ComputeRand.test{1} = None /\
  mSk_inv AKE_find.mSk{2} /\
  AKE_find.sH2'{2} = FSet.empty /\
  AKE_find.sKeyRev{2} = FSet.empty /\
  AKE_find.mKeyRev{2} = Map.empty /\
  univ_map AKE_find.mEexp{2}).
while (  ={sidxs} /\
AKE_ComputeRand.mEexp{1} = AKE_find.mEexp{2}  /\
  (forall (s : Sidx), !mem s sidxs{2} => in_dom s AKE_find.mEexp{2})).
 wp; rnd; wp; skip; progress => //.
 generalize H5; rewrite mem_rm not_and => [|] h.
 by rewrite in_dom_set; left; apply H.
 rewrite in_dom_set; right; smt.
 while (={pks, i} /\   AKE_ComputeRand.mSk{1} = AKE_find.mSk{2} /\ 
         mSk_inv AKE_find.mSk{2} ).
 wp; rnd; skip; progress => //.
 rewrite /mSk_inv => s; rewrite in_dom_set.
  case (gen_pk skaL = s).
  by intros => <- _; rewrite get_setE proj_some.
  intros => h [|] h'; last smt.
  by rewrite get_setNE //; apply H.
 inline AKE_ComputeRand(A).init AKE_find(A).init.
 by wp; skip; progress; smt.
 if => //; last by rnd; skip; progress => //.
seq 1 1:
  ( ={glob A} /\
  AKE_find.t_idx{2} = AKE_ComputeRand.t_idx{1} /\
  AKE_find.evs{2} = AKE_ComputeRand.evs{1} /\
  AKE_find.test{2} = AKE_ComputeRand.test{1} /\
  AKE_find.cSession{2} = AKE_ComputeRand.cSession{1} /\
  AKE_find.cH2{2} = AKE_ComputeRand.cH2{1} /\
  AKE_find.sH2{2} = AKE_ComputeRand.sH2{1} /\
  AKE_find.mSk{2} = AKE_ComputeRand.mSk{1} /\
  AKE_find.mEexp{2} = AKE_ComputeRand.mEexp{1} /\
  AKE_find.mStarted{2} = AKE_ComputeRand.mStarted{1} /\
  AKE_find.mCompleted{2} = AKE_ComputeRand.mCompleted{1} /\
  (is_dom AKE_find.sH2' AKE_find.mH2){2} /\
  (is_dom AKE_find.sKeyRev AKE_find.mKeyRev){2} /\
  inv_split_dom AKE_ComputeRand.mH2{1} AKE_find.mH2{2} AKE_find.mKeyRev{2} 
                AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                AKE_find.mSk{2} /\
  inv_split_val1 AKE_ComputeRand.mH2{1} AKE_find.mH2{2} /\
  inv_split_val2 AKE_ComputeRand.mH2{1} AKE_find.mKeyRev{2} 
                 AKE_find.mStarted{2} AKE_find.mCompleted{2} AKE_find.mEexp{2}
                 AKE_find.mSk{2} /\
  is_sub_map AKE_find.mCompleted{2} AKE_find.mStarted{2} /\
  is_sub_map AKE_find.mKeyRev{2} AKE_find.mCompleted{2} /\ 
  univ_map AKE_find.mEexp{2} /\
  actor_valid AKE_find.mStarted{2} AKE_find.mCompleted{2} 
              AKE_find.mEexp{2} AKE_find.mSk{2} /\
  mSk_inv AKE_find.mSk{2} /\
  univ_map AKE_find.mEexp{2}).
call AKE_RandCompute_Eqs_choose; skip; progress => //.
 rewrite /is_dom; smt. 
 rewrite /is_dom; smt.
 rewrite /inv_split_dom; smt.
 rewrite /inv_split_val2; smt.
 rewrite /is_sub_map; smt.
 rewrite /is_sub_map; smt.
 rewrite /actor_valid; smt.
 if => //; last by rnd.
  rnd; call AKE_RandCompute_Eqs_guess; wp; rnd; wp; skip; progress => //.
save.


local lemma Pr4 : forall &m,
Pr[AKE_ComputeRand(A).main() @ &m : 
AKE_ComputeRand.test <> None /\ 
in_dom AKE_ComputeRand.t_idx AKE_ComputeRand.mCompleted /\ 
mem
(get_string_from_id AKE_ComputeRand.t_idx AKE_ComputeRand.mStarted 
  AKE_ComputeRand.mCompleted AKE_ComputeRand.mEexp AKE_ComputeRand.mSk) 
AKE_ComputeRand.sH2 /\
fresh_op (compute_sid AKE_ComputeRand.mStarted AKE_ComputeRand.mEexp 
                      AKE_ComputeRand.mCompleted AKE_ComputeRand.t_idx)  
        AKE_ComputeRand.evs] =
Pr[AKE_find(A).main() @ &m : 
AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\ 
mem (get_string_from_id AKE_find.t_idx AKE_find.mStarted AKE_find.mCompleted 
                        AKE_find.mEexp AKE_find.mSk) AKE_find.sH2 /\ 
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs].
proof strict.
 intros => &m.
 by equiv_deno AKE_RandCompute_Eqs.
save.

local lemma Pr_sofar2 : forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
1%r/2%r + 
Pr[AKE_find(A).main() @ &m : 
AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\ 
mem
(get_string_from_id AKE_find.t_idx AKE_find.mStarted 
  AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) 
AKE_find.sH2 /\
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs].
proof strict. 
 intros => &m.
 rewrite -(Pr4 &m).
 apply (Pr_sofar1 &m).
save.


local module AKE2toAKE3(O3 : AKE_Oracles3) : Adv3(O3) = {
  var evs  : Event list               (* events for queries performed by adversary *)
  var test : Sid option               (* session id of test session *)

  var cH2 : int        (* counters for queries *)

  var mH2 : (Sstring, Key) map        (* map for h2 *)
  var sH2 : Sstring set               (* adversary queries for h2 *)

  var mStarted   : (Sidx, Sdata2) map (* map of started sessions *)
  var mEPK       : (Sidx, Epk) map (* in_dom i mEPK => 
                                         mEPK.[i] =gen_exp (mEexp.[i]) *)
  var mCompleted : (Sidx, Epk)   map  (* additional data for completed sessions *)
  var mKeyRev    : (Sidx, Key) map    (* maps id's to revealed keys *)
  var sKeyRev    : Sidx set           (* set of id's revealed (dom of mKeyrev) *)
  var sH2'       : Sstring set        (* exactly dom(mH2) *)
  var t_idx : Sidx  


  module O2 : AKE_Oracles2 = {
    fun eexpRev(i : Sidx, a : Sk) : Eexp option = {
      var r : Eexp option = None;
      var p1 : Agent = def;
      var p2 : Agent;
      var pr : Role;
      var msgX : Epk;
      if (in_dom i mStarted) {
       (p1, p2, pr) = proj (mStarted.[i]);
       msgX = proj mEPK.[i];
       if (test <> None => fresh_op (proj test) 
               (EphemeralRev(p1, p2, msgX, pr)::evs )) {
        r = O3.eexpRev(i,a);
        evs =EphemeralRev(p1, p2, msgX, pr)::evs;
     }
    }
      return r;
   }

    fun find_id (sstr : Sstring, s : Sidx set) : Sidx option = {
      var aux : Sidx set = s;
      var ret = None;
      var i : Sidx = def;
      var b : bool option = None;
      while (aux <> FSet.empty /\ ret = None) {
       i = pick aux;
       aux = rm i aux;
       b = O3.eqS(i, sstr);
       ret = (b <> None && (proj b)) ? Some i : None;
     }
     return ret;
    }
    
    fun h2(sstring : Sstring) : Key = {
      var ke : Key;
      var s : Sidx option = None;
      var ret : Key;
      ke = $sample_Key;
      if (in_dom sstring mH2) {
        ret = proj mH2.[sstring];
      } else {
       s = find_id(sstring, sKeyRev);
       if (s <> None) { ret = proj mKeyRev.[proj s];}
       else {
        ret = ke;
        mH2.[sstring] = ke;
        sH2' = add sstring sH2';
       }
      }
      return ret;
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
      r = O3.init1(i, A, B);
      if (r <> None) {
        pX = proj r;
        evs = Start((A,B,pX,init))::evs;
        mStarted.[i] = (A,B,init);
        mEPK.[i] = pX;
      }
      return r;
    }

    fun resp(i : Sidx, B : Agent, A : Agent, X : Epk) : Epk option = {
      var pY : Epk;
      var r : Epk option = None;
      r = O3.resp(i, B, A, X);
      if (r <> None) {
        pY = proj r;
        mStarted.[i] = (B,A,resp);
        mCompleted.[i] = X;
        mEPK.[i] = pY;
        evs = Accept((B,A,pY,X,resp))::evs;
      }
      return r;
    }

    fun init2(i : Sidx, Y : Epk) : unit = {
      var p1, p2 : Agent;
      var r : Role;
      var msgX : Epk;
      if (!in_dom i mCompleted /\ in_dom i mStarted) {
      (p1, p2, r) = proj mStarted.[i];
      msgX = proj mEPK.[i];
       if (test <> None => fresh_op (proj test) 
               (Accept(p1, p2, msgX, Y, r)::evs )) {
          mCompleted.[i] = Y;
          evs = Accept(p1, p2, msgX, Y, r)::evs;
          O3.init2(i, Y);
      }
     }
    }

    fun staticRev(A : Agent) : Sk option = {
      var r : Sk option = None;
      if (((test <> None => 
        fresh_op (proj test) (StaticRev A::evs )))) {
        r = O3.staticRev(A);
        if (r <> None) evs = StaticRev(A)::evs;
      }
      return r;
    }

    fun find_string (id : Sidx, sstr : Sstring set) : Sstring option = {
      var aux : Sstring set = sstr;
      var ret = None;
      var str : Sstring = def;
      var b : bool option = None;
      while (aux <> FSet.empty /\ ret = None) {
       str = pick aux;
       aux = rm str aux;
       b = O3.eqS(id, str);
       ret = (b <> None && (proj b)) ? Some str : None;
     }
     return ret;
    }
    
    fun find_matching (id : Sidx, id_set : Sidx set) : Sidx option = {
     var p1, p2 : Agent;
     var mX, mY : Epk;
     var r : Role;
     var sid, sid' : Sid;
     var aux = id_set;
     var ret = None;
     var j : Sidx;
     (p1, p2, r) = proj mStarted.[id];
     mX = proj mEPK.[id];
     mY = proj mCompleted.[id];
     sid = (p1, p2, mX, mY, r);
     while (aux <> FSet.empty /\ ret = None) {
      j = pick aux;
      aux = rm j aux;
      (p1, p2, r) = proj mStarted.[j];
      mX = proj mEPK.[j];
      mY = proj mCompleted.[j];
      sid' = (p1, p2, mX, mY, r);
      if (sid' = sid \/ cmatching sid' = sid ) ret = Some j;
     }
     return ret;
    }

    fun computeKey(i : Sidx) : Key option = {
      var r : Key option = None;
      var k : Key;
      var ret = None;
      var str = None; 
      var j : Sidx option;
      if (in_dom i mCompleted) {
        k = $sample_Key;
        if (in_dom i mKeyRev) {
         ret = mKeyRev.[i];
        } else {
         j = find_matching (i, sKeyRev);
         if (j <> None) {
          ret = mKeyRev.[proj j];
         } else {
          str = find_string (i, sH2');
          if (str <> None) {
           ret = mH2.[proj str];
          } else {
           ret = Some k;
           mKeyRev.[i] = k;
           sKeyRev = add i sKeyRev;
          }
         }
        }
       }
    return ret;
   }

    fun sessionRev(i : Sidx) : Key option = {
     var r : Key option = None;
     var p1, p2 : Agent;
     var mX, mY : Epk;
     var r' : Role;
     var sid : Sid;
     if (in_dom i mCompleted) {
      (p1, p2, r') = proj mStarted.[i];
      mX = proj mEPK.[i];
      mY = proj mCompleted.[i];
      sid = (p1, p2, mX, mY, r');
      if ((test <> None) => fresh_op (proj test) ((SessionRev sid)::evs) ) {
        r = computeKey(i);
        evs = SessionRev(sid)::evs;
      }
     }
       return r;
   }
 }
 fun init() : unit ={
  evs = [];
  test = None;
  mH2 = Map.empty;
  sH2 = FSet.empty;
  mStarted = Map.empty;
  mEPK = Map.empty;
  mCompleted = Map.empty;
  mKeyRev = Map.empty;
  sKeyRev = FSet.empty;
  sH2' = FSet.empty;
  t_idx = def;
  cH2 = 0;
 }
 module FA = A(O2)
 fun guess(s : Pk list) : (Sstring list * Sidx) = {
  var p1, p2 : Agent;
  var mX, mY : Epk;
  var r' : Role;
  var sid : Sid;
  var b : bool;
  var key : Key;
  init();
  t_idx = FA.choose(s);
  if (mStarted.[t_idx] <> None && mCompleted.[t_idx] <> None) {
      (p1, p2, r') = proj mStarted.[t_idx];
      mX = proj mEPK.[t_idx];
      mY = proj mCompleted.[t_idx];
      sid = (p1, p2, mX, mY, r'); 
      if (fresh_op sid evs) {
       test = Some sid;
       key  = $sample_Key;
       b = FA.guess(Some key);
      }
   }
   return (FSet.elems sH2, t_idx);
  }
}.

require import Pair.

pred inv_EPK (mEexp : (Sidx, Eexp)  map) mEPK = 
forall (i : Sidx), in_dom i mEPK => proj mEPK.[i] = gen_epk (proj mEexp.[i]).

pred inv_KeyRev (mKeyRev: (Sidx, Key) map) (evs : Event list) (mStarted :  (Sidx, Sdata2) map)
                 (mCompleted : (Sidx, Epk) map) mEexp =
forall i, in_dom i mKeyRev => mem (SessionRev (compute_sid mStarted mEexp mCompleted i)) evs.


local equiv AKE_find_eqS_find_id : 
AKE_find(A).O.find_id ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.find_id :
   ={sstr, s} /\
   is_dom s{1} AKE_find.mKeyRev{1} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\
   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun.
 sp; wp.
 inline AKE_eqS(AKE2toAKE3).O.eqS AKE_find(A).O.eqS.
 while ( ={i, b, ret, aux, sstr} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
   AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
   (forall x, mem x aux{1} => mem x s{1}) /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
   is_dom s{1} AKE_find.mKeyRev{1} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}) => //.
  wp; skip; progress => //.
   by apply tr_sim_dup_sRev => //; apply H10; rewrite H9 H7 //; apply mem_pick . 
   by apply H7; generalize H17; rewrite mem_rm.
   by apply H7; generalize H17; rewrite mem_rm.
   by apply H7; generalize H14; rewrite mem_rm.
save.

local equiv AKE_find_eqS_find_string : 
AKE_find(A).O.find_string ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.find_string :
   ={id, sstr} /\
  (mem (SessionRev (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id)) AKE_find.evs){1} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun; sp; wp. 
 while (   ={id, sstr, str, b, ret, aux} /\
   (mem (SessionRev (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted id)) AKE_find.evs){1} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}) => //.
  inline AKE_find(A).O.eqS AKE_eqS(AKE2toAKE3).O.eqS.
  wp; skip; progress => //.
   apply tr_sim_dup_sRev => //.
save.

local equiv AKE_find_eqS_find_matching : 
AKE_find(A).O.find_matching ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.find_matching :
   ={id, id_set} /\
  in_dom id{1} AKE_find.mCompleted{1} /\
   id_set{1} = AKE_find.sKeyRev{1} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun; wp; sp.
 while 
  (={id, id_set, ret, aux, sid} /\
  (forall x,  mem x aux{1} => mem x AKE_find.sKeyRev{1}) /\
  in_dom id{1} AKE_find.mCompleted{1} /\
  id_set{1} = AKE_find.sKeyRev{1} /\
  AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
  AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
  AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
  AKE_find.test{1} = AKE2toAKE3.test{2} /\
  AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
  AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
  AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
  AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
  AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
  AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
  AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
  AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
  AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
  univ_map AKE_eqS.mEexp{2} /\
  mSk_inv AKE_eqS.mSk{2} /\
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
    AKE_find.mCompleted{1} AKE_find.mEexp{1}).
  wp; skip; progress => //.
   by apply H; generalize H16; rewrite mem_rm.
   (cut : false; last smt); generalize H15 => /=.
   elim H14 => h {H14}; [left | right].
   rewrite /compute_sid H13 /= -h.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   rewrite /compute_sid H13 -h  /cmatching /=.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   by apply H; generalize H16; rewrite mem_rm.
   (cut : false; last smt); generalize H15 => /=.
   elim H14 => h {H14}; [left | right].
   rewrite /compute_sid H13 /= -h.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   rewrite /compute_sid H13 -h  /cmatching /=.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   (cut : false; last smt); generalize H14 => /=.
   elim H15 => h {H15}; [left | right].
   rewrite -h /compute_sid H13 /= .
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   rewrite  -h /compute_sid H13  /cmatching /=.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   (cut : false; last smt); generalize H14 => /=.
   elim H15 => h {H15}; [left | right].
   rewrite -h /compute_sid H13 /= .
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   rewrite  -h /compute_sid H13  /cmatching /=.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   (cut : false; last smt); generalize H14 => /=.
   elim H15 => h {H15}; [left | right].
   rewrite -h /compute_sid H13 /= .
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   rewrite  -h /compute_sid H13  /cmatching /=.
   rewrite H4 => //. 
   by apply H7; apply H5; apply H8; rewrite H9; apply H; apply mem_pick.
   by apply H; generalize H16; rewrite mem_rm.
   skip; progress.
   rewrite /compute_sid -H /= H4 //.
   by apply H7; apply H5.
save.

local equiv AKE_find_eqS_h2 : 
AKE_find(A).O.h2 ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.h2 :
   ={sstring} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun.
 sp.
 seq 1 1: (s{2} = None /\
  s{1} = None /\
  ={sstring, ke} /\
  AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
  AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
  AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
  AKE_find.test{1} = AKE2toAKE3.test{2} /\

  AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
  AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
  AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
  AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
  AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
  AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
  AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
  AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
  AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
  univ_map AKE_eqS.mEexp{2} /\
  mSk_inv AKE_eqS.mSk{2} /\
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
    AKE_find.mCompleted{1} AKE_find.mEexp{1}).
 by rnd.
 if => //.
  by wp; skip; progress.
  seq 1 1:
(  ={s,sstring, ke} /\
   AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\
   mSk_inv AKE_eqS.mSk{2} /\
   inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
   is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
   is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
   is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
   inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
     AKE_find.mCompleted{1} AKE_find.mEexp{1} /\
  ! in_dom sstring{1} AKE_find.mH2{1}).
  call AKE_find_eqS_find_id; skip; progress.
  by wp; skip; progress.
save.

local equiv AKE_find_eqS_h2_a : 
AKE_find(A).O.h2_a ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.h2_a :
   ={sstring} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 by fun; sp; if => //; wp; call AKE_find_eqS_h2; wp; skip; progress.
save.

local equiv AKE_find_eqS_computeKey : 
AKE_find(A).O.computeKey ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.computeKey :
   ={i} /\
   (mem (SessionRev (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted i)) AKE_find.evs){1} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
fun.
sp.
if => //.
seq 1 1:
(
  (str{2} = None /\
   ret{2} = None /\
   r{2} = None /\
   str{1} = None /\
   ret{1} = None /\
   r{1} = None /\
   ={i, k} /\
   mem
     (SessionRev
        (compute_sid AKE_find.mStarted{1} AKE_find.mEexp{1}
           AKE_find.mCompleted{1} i{1})) AKE_find.evs{1} /\
   AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
   AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\
   mSk_inv AKE_eqS.mSk{2} /\
   inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
   is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
   is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
   is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
   is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
   is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
   inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
     AKE_find.mCompleted{1} AKE_find.mEexp{1}) /\
  in_dom i{1} AKE_find.mCompleted{1}).
by rnd.
if => //.
by wp.
seq 1 1:
(
  ((ret{2} = None /\
    r{2} = None /\
    ret{1} = None /\
    r{1} = None /\
    ={k, i, str, j} /\ 
    mem
      (SessionRev
         (compute_sid AKE_find.mStarted{1} AKE_find.mEexp{1}
            AKE_find.mCompleted{1} i{1})) AKE_find.evs{1} /\
    AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
    AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
    AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
    tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
    AKE_find.test{1} = AKE2toAKE3.test{2} /\
 
    AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
    AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
    AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
    AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
    AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
    AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
    AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
    AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
    AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
    univ_map AKE_eqS.mEexp{2} /\
    mSk_inv AKE_eqS.mSk{2} /\
    inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
    is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
    is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
    is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
    is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
    is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
    inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
      AKE_find.mCompleted{1} AKE_find.mEexp{1}) /\
   in_dom i{1} AKE_find.mCompleted{1}) /\
  ! in_dom i{1} AKE_find.mKeyRev{1}).
call AKE_find_eqS_find_matching.
skip; progress => //.
if => //.
wp; skip; progress.
seq 1 1:
 (((ret{2} = None /\
     r{2} = None /\
     ret{1} = None /\
     r{1} = None /\
     ={k, i, str, j} /\
     mem
       (SessionRev
          (compute_sid AKE_find.mStarted{1} AKE_find.mEexp{1}
             AKE_find.mCompleted{1} i{1})) AKE_find.evs{1} /\
     AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
     AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
     AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
     AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
     tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
     AKE_find.test{1} = AKE2toAKE3.test{2} /\
  
     AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
     AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
     AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
     AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
     AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
     AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
     AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
     AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
     AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
     univ_map AKE_eqS.mEexp{2} /\
     mSk_inv AKE_eqS.mSk{2} /\
     inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
     is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
     is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
     is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
     is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
     is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
     inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
       AKE_find.mCompleted{1} AKE_find.mEexp{1}) /\
    in_dom i{1} AKE_find.mCompleted{1}) /\
   ! in_dom i{1} AKE_find.mKeyRev{1} /\
  ! ! j{1} = None).
call AKE_find_eqS_find_string.
skip; progress => //.
if => //.
wp; skip; progress => //.
wp; skip; progress => //.
by apply is_sub_map_upd3.
by apply is_dom_add.
intros => j.
rewrite  in_dom_set => [|] // hj.
cut := H9 j _ => //.
save.

local equiv AKE_find_eqS_sessionRev : 
AKE_find(A).O.sessionRev ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).O2.sessionRev :
   ={i} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
   ={res} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
fun.
 sp.
 if{1}.
 rcondt{2} 1 => //.
 rcondt{2} 5.
  intros => ?; wp; skip; progress.
  rewrite (_ : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}],
      proj AKE2toAKE3.mCompleted{hr}.[i{hr}], x3) =  (compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
             AKE2toAKE3.mCompleted{hr} i{hr})) //.
 rewrite /compute_sid H11 /= H2 //.
 by apply H5; apply H3.
 by apply H10.
 swap{2} 6 -1.
 call AKE_find_eqS_computeKey.
 wp; skip; progress => //.
  by rewrite mem_cons; left.
  by rewrite /compute_sid H11 /= H2 //; apply H5; apply H3.
  by apply tr_sim_skip_sRev.
  intros => j hj.
  by cut := H8 j _ => //; rewrite mem_cons => h; right.
  if{2}.
  rcondf{2} 5 => //.
   intros => &m; wp; skip; progress.
rewrite (_ : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}],
         proj AKE2toAKE3.mCompleted{hr}.[i{hr}], x3) = 
(compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
                AKE2toAKE3.mCompleted{hr} i{hr})) .
rewrite /compute_sid H11 /= H2 //.
by apply H5; apply H3.
smt.
wp; skip; progress.
wp; skip; progress.
save.

local equiv AKE_find_eqS_guess : 
AKE_find(A).A.guess ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).FA.guess :
={k, glob A} /\
AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
={res, glob A} /\
AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun (AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}) => //.
fun.
inline AKE_eqS(AKE2toAKE3).O.eexpRev.
seq 1 2: (={i, a, r} /\
  r{2} = None /\
  AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
  AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
  AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
  AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
  tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
  AKE_find.test{1} = AKE2toAKE3.test{2} /\

  AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
  AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
  AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
  AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
  AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
  AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
  AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
  AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
  AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
  univ_map AKE_eqS.mEexp{2} /\
  mSk_inv AKE_eqS.mSk{2} /\
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
    AKE_find.mCompleted{1} AKE_find.mEexp{1}).
wp; skip; progress => //.
if{1}; last first.
if{2}.
rcondf{2} 3 => //.
intros => ?; wp; skip; progress.
cut : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], x3) = 
(compute_psid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr} i{hr}).
rewrite /compute_psid  H11 H2 /= //; first by apply H5.
smt.
wp; skip; progress => //.
skip; progress => //.
rcondt{2} 1.
intros => ?; skip; progress => //.
rcondt{2} 3.
intros => ?; wp; skip; progress => //.
cut : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], x3) = 
(compute_psid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr} i{hr}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
smt.
rcondt{2} 6.
intros => ?; wp; skip; progress => //.
wp; skip; progress => //.

cut : (x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], x3) = 
(compute_psid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} i{2}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
smt.
cut <- : (x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], x3) = 
(compute_psid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} i{2}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right; by apply H8.
by rewrite /compute_psid /= H11 /= H2 //; apply H5. 
rewrite /compute_psid /= H11 /= H2 //; first by apply H5.
by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right; by apply H8.

apply AKE_find_eqS_h2_a.

fun.
inline  AKE_eqS(AKE2toAKE3).O.init1.
sp.
if => //; last first.
sp.
rcondf{2} 1.
by intros => ?; skip.
skip; progress.
rcondt{2} 6.
by intros => ?; wp; skip; progress => //; smt.
wp; skip; progress => //.
by rewrite proj_some.
by rewrite proj_some; apply tr_sim_eq_ev.
rewrite proj_some /inv_EPK => j.
case (j = i{2}) => heq.
 by rewrite heq get_setE proj_some.
 rewrite in_dom_setNE // get_setNE; first smt.
 by intros => h; apply H2.
 by apply is_sub_map_upd1. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
intros => j hj; rewrite mem_cons; right.
cut ->: ((compute_sid AKE2toAKE3.mStarted{2}.[i{2} <- (A{2}, B{2}, init)]
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j) = 
        (compute_sid AKE2toAKE3.mStarted{2}
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j)).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H11 => /=.
rewrite h.
by apply H3; apply H6.
rewrite /compute_sid.
rewrite  get_setNE //.
by  apply H8.

fun.
inline AKE_eqS(AKE2toAKE3).O.init2.
if{1}; last first.
if{2}=> //.
rcondf{2} 3.
intros => ?; wp; skip; progress => //.
cut: ((x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], Y{hr}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
                AKE2toAKE3.mCompleted{hr}.[i{hr} <- Y{hr}] i{hr})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
wp; progress => //.
rcondt{2} 1.
intros => ?; skip; progress => //.
rcondt{2} 3.
intros => ?; wp; skip; progress => //.
cut: ((x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], Y{hr}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
                AKE2toAKE3.mCompleted{hr}.[i{hr} <- Y{hr}] i{hr})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
rcondt{2} 7.
intros => ?; wp; skip; progress => //.
 wp; skip; progress => //. 
cut: ((x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], Y{2}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
                AKE2toAKE3.mCompleted{2}.[i{2} <- Y{2}] i{2})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
 rewrite /compute_sid H12 /= get_setE proj_some H2 //; first apply H5 => //.
 by apply tr_sim_eq_ev.
 by apply is_sub_map_upd3. 
 by apply is_sub_map_upd1. 
intros => j hj; rewrite mem_cons; right.
cut ->: (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
        AKE2toAKE3.mCompleted{2}.[i{2} <- Y{2}] j) =
       (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
        AKE2toAKE3.mCompleted{2} j).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H9 => /=.
rewrite h.
by  apply H6.
rewrite /compute_sid.
rewrite  get_setNE //.
by  apply H8.

fun.
inline AKE_eqS(AKE2toAKE3).O.resp.
sp.
if => //; last first.
sp.
rcondf{2} 1.
intros => ?; wp; skip; progress => //.
skip; progress => //.
rcondt{2} 7.
intros => ?; wp; skip; progress => //; smt.
wp; skip; progress => //.
by rewrite proj_some.
by rewrite proj_some; apply tr_sim_eq_ev.
rewrite /inv_EPK => j.
case (j = i{2}) => heq.
 by rewrite heq get_setE !proj_some.
 rewrite in_dom_setNE // get_setNE; first smt.
 by intros => h; apply H2.
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd1. 
intros => j hj; rewrite mem_cons; right.
cut ->: (compute_sid AKE2toAKE3.mStarted{2}.[i{2} <- (B{2}, A{2}, resp)]
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2}.[i{2} <- X{2}] j) =
       (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H12 => /=.
rewrite h.
by  apply H6.
rewrite /compute_sid.
rewrite  !get_setNE //.
by  apply H8.

 fun; inline AKE_eqS(AKE2toAKE3).O.staticRev.
 wp; skip; progress.
 by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right.
by apply H8.

 generalize H10 H11; rewrite /in_dom; smt.
 generalize H10 H11; rewrite /in_dom; smt.
 generalize H10 H11; rewrite /in_dom; smt.
 apply AKE_find_eqS_sessionRev.
save.

local equiv AKE_find_eqS_choose : 
AKE_find(A).A.choose ~ AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).FA.choose :
={s, glob A} /\
AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1} ==>
={res, glob A} /\
AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}.
proof strict.
 fun (AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2}  /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1} AKE_find.mCompleted{1} AKE_find.mEexp{1}) => //.
fun.
inline AKE_eqS(AKE2toAKE3).O.eexpRev.
seq 1 2: (={i, a, r} /\
  r{2} = None /\
  AKE_find.sH2'{1} = AKE2toAKE3.sH2'{2} /\
  AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
  AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
  AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
  tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
  AKE_find.test{1} = AKE2toAKE3.test{2} /\

  AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
  AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
  AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
  AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
  AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
  AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
  AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
  AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
  AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
  univ_map AKE_eqS.mEexp{2} /\
  mSk_inv AKE_eqS.mSk{2} /\
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  inv_KeyRev AKE_find.mKeyRev{1} AKE_find.evs{1} AKE_find.mStarted{1}
    AKE_find.mCompleted{1} AKE_find.mEexp{1}).
wp; skip; progress => //.
if{1}; last first.
if{2}.
rcondf{2} 3 => //.
intros => ?; wp; skip; progress.
cut : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], x3) = 
(compute_psid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr} i{hr}).
rewrite /compute_psid  H11 H2 /= //; first by apply H5.
smt.
wp; skip; progress => //.
skip; progress => //.
rcondt{2} 1.
intros => ?; skip; progress => //.
rcondt{2} 3.
intros => ?; wp; skip; progress => //.
cut : (x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], x3) = 
(compute_psid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr} i{hr}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
smt.
rcondt{2} 6.
intros => ?; wp; skip; progress => //.
wp; skip; progress => //.

cut : (x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], x3) = 
(compute_psid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} i{2}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
smt.
cut <- : (x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], x3) = 
(compute_psid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} i{2}).
rewrite /compute_psid  H11 H2 //; first by apply H5.
by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right; by apply H8.
by rewrite /compute_psid /= H11 /= H2 //; apply H5. 
rewrite /compute_psid /= H11 /= H2 //; first by apply H5.
by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right; by apply H8.


fun.
inline  AKE_eqS(AKE2toAKE3).O.init1.
sp.
if => //; last first.
sp.
rcondf{2} 1.
by intros => ?; skip.
skip; progress.
rcondt{2} 6.
by intros => ?; wp; skip; progress => //; smt.
wp; skip; progress => //.
by rewrite proj_some.
by rewrite proj_some; apply tr_sim_eq_ev.
rewrite proj_some /inv_EPK => j.
case (j = i{2}) => heq.
 by rewrite heq get_setE proj_some.
 rewrite in_dom_setNE // get_setNE; first smt.
 by intros => h; apply H2.
 by apply is_sub_map_upd1. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
intros => j hj; rewrite mem_cons; right.
cut ->: ((compute_sid AKE2toAKE3.mStarted{2}.[i{2} <- (A{2}, B{2}, init)]
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j) = 
        (compute_sid AKE2toAKE3.mStarted{2}
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j)).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H11 => /=.
rewrite h.
by apply H3; apply H6.
rewrite /compute_sid.
rewrite  get_setNE //.
by  apply H8.

fun.
inline AKE_eqS(AKE2toAKE3).O.init2.
if{1}; last first.
if{2}=> //.
rcondf{2} 3.
intros => ?; wp; skip; progress => //.
cut: ((x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], Y{hr}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
                AKE2toAKE3.mCompleted{hr}.[i{hr} <- Y{hr}] i{hr})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
wp; progress => //.
rcondt{2} 1.
intros => ?; skip; progress => //.
rcondt{2} 3.
intros => ?; wp; skip; progress => //.
cut: ((x1, x2, proj AKE2toAKE3.mEPK{hr}.[i{hr}], Y{hr}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{hr} AKE_eqS.mEexp{hr}
                AKE2toAKE3.mCompleted{hr}.[i{hr} <- Y{hr}] i{hr})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
rcondt{2} 7.
intros => ?; wp; skip; progress => //.
 wp; skip; progress => //. 
cut: ((x1, x2, proj AKE2toAKE3.mEPK{2}.[i{2}], Y{2}, x3) = 
      (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
                AKE2toAKE3.mCompleted{2}.[i{2} <- Y{2}] i{2})).
rewrite /compute_sid H12 /= get_setE proj_some H2 //; by apply H5.
smt.
 rewrite /compute_sid H12 /= get_setE proj_some H2 //; first apply H5 => //.
 by apply tr_sim_eq_ev.
 by apply is_sub_map_upd3. 
 by apply is_sub_map_upd1. 
intros => j hj; rewrite mem_cons; right.
cut ->: (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
        AKE2toAKE3.mCompleted{2}.[i{2} <- Y{2}] j) =
       (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2}
        AKE2toAKE3.mCompleted{2} j).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H9 => /=.
rewrite h.
by  apply H6.
rewrite /compute_sid.
rewrite  get_setNE //.
by  apply H8.

fun.
inline AKE_eqS(AKE2toAKE3).O.resp.
sp.
if => //; last first.
sp.
rcondf{2} 1.
intros => ?; wp; skip; progress => //.
skip; progress => //.
rcondt{2} 7.
intros => ?; wp; skip; progress => //; smt.
wp; skip; progress => //.
by rewrite proj_some.
by rewrite proj_some; apply tr_sim_eq_ev.
rewrite /inv_EPK => j.
case (j = i{2}) => heq.
 by rewrite heq get_setE !proj_some.
 rewrite in_dom_setNE // get_setNE; first smt.
 by intros => h; apply H2.
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd2. 
 by apply is_sub_map_upd1. 
intros => j hj; rewrite mem_cons; right.
cut ->: (compute_sid AKE2toAKE3.mStarted{2}.[i{2} <- (B{2}, A{2}, resp)]
        AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2}.[i{2} <- X{2}] j) =
       (compute_sid AKE2toAKE3.mStarted{2} AKE_eqS.mEexp{2} AKE2toAKE3.mCompleted{2} j).
case (i{2} = j) => h .
cut: false; last by smt.
generalize H12 => /=.
rewrite h.
by  apply H6.
rewrite /compute_sid.
rewrite  !get_setNE //.
by  apply H8.

 fun; inline AKE_eqS(AKE2toAKE3).O.staticRev.
 wp; skip; progress.
 by apply tr_sim_eq_ev.
intros => j hj; rewrite mem_cons; right.
by apply H8.

 generalize H10 H11; rewrite /in_dom; smt.
 generalize H10 H11; rewrite /in_dom; smt.
 generalize H10 H11; rewrite /in_dom; smt.
 apply AKE_find_eqS_h2_a.
 apply AKE_find_eqS_sessionRev.
save.

local equiv AKE_find_eqS : 
AKE_find(A).main ~ AKE_eqS(AKE2toAKE3).main :
={glob A} ==>
(AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\
mem
(get_string_from_id AKE_find.t_idx AKE_find.mStarted 
  AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) 
AKE_find.sH2 /\
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs){1} =>
(
in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs){2}.
 fun.
 inline AKE_eqS(AKE2toAKE3).init AKE_find(A).init AKE_eqS(AKE2toAKE3).A.guess.
seq 27 19 : 
 (={b, pks, key, keyo, b', i, glob A} /\
  AKE_find.sH2'{1} = FSet.empty /\
  AKE_find.sKeyRev{1} = FSet.empty /\
  AKE_find.mKeyRev{1} = Map.empty /\
  AKE_find.evs{1} = AKE_eqS.evs{2} /\
  AKE_find.evs{1} = [] /\
  AKE_find.test{1} = None /\

  AKE_find.cSession{1} = 0 /\
  AKE_find.cH1{1} = 0 /\
  AKE_find.cH2{1} = 0 /\
  AKE_find.mH2{1} = Map.empty /\
  AKE_find.sH2{1} = FSet.empty /\
  AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
  AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
  AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\ 
  AKE_find.mStarted{1} = Map.empty /\
  AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\ 
  AKE_find.mCompleted{1} = Map.empty /\
  univ_map AKE_eqS.mEexp{2} /\
  mSk_inv AKE_eqS.mSk{2} ). 
while (  ={sidxs} /\
AKE_find.mEexp{1} = AKE_eqS.mEexp{2}  /\
  (forall (s : Sidx), !mem s sidxs{2} => in_dom s AKE_eqS.mEexp{2})).
 wp; rnd; wp; skip; progress => //.
 generalize H5; rewrite mem_rm not_and => [|] h.
 by rewrite in_dom_set; left; apply H.
 rewrite in_dom_set; right; smt.
 while (={pks, i} /\   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\ 
         mSk_inv AKE_eqS.mSk{2} ).
 wp; rnd; wp; skip; progress.
 rewrite /mSk_inv => s; rewrite in_dom_set.
  case (gen_pk skaL = s).
  by intros => <- _; rewrite get_setE proj_some.
  intros => h [|] h'; last smt.
  by rewrite get_setNE //; apply H.
wp; skip; progress.
 rewrite /mSk_inv; smt.
 smt.
 rewrite /univ_map => x; apply H2; smt.
 if => //; last first.
 rnd{1}; skip; progress => //; smt.

 inline AKE2toAKE3(AKE_eqS(AKE2toAKE3).O).init.
 seq 0 13:
 (={b, pks, key, keyo, b', i, glob A} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
   AKE_find.evs{1} = AKE_eqS.evs{2} /\
   AKE_find.evs{1} = [] /\
   AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cSession{1} = 0 /\
   AKE_find.cH1{1} = 0 /\
   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\
  ! collision_eexp_eexp_op AKE_find.mEexp{1} /\
   s{2} = pks{2}  /\ 
  inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2} /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
  AKE2toAKE3.mKeyRev{2} = Map.empty).
  wp; skip; progress => //.
 rewrite /inv_EPK; smt.
 rewrite /is_sub_map; smt.
 rewrite /is_sub_map; smt.
 rewrite /is_sub_map; smt.
 rewrite /is_sub_map; smt.
 rewrite /is_dom; smt.
seq 1 1:
(={b, pks, key, keyo, b', i, glob A} /\
   AKE_find.sH2'{1} =  AKE2toAKE3.sH2'{2} /\
   AKE_find.sKeyRev{1} = AKE2toAKE3.sKeyRev{2} /\
   AKE_find.mKeyRev{1} = AKE2toAKE3.mKeyRev{2} /\
    AKE_find.evs{1} = AKE2toAKE3.evs{2} /\
   tr_sim AKE2toAKE3.evs{2} AKE_eqS.evs{2} /\
   AKE_find.test{1} = AKE2toAKE3.test{2} /\

   AKE_find.cH2{1} = AKE2toAKE3.cH2{2} /\
   AKE_find.mH2{1} = AKE2toAKE3.mH2{2} /\
   AKE_find.sH2{1} = AKE2toAKE3.sH2{2} /\
   AKE_find.mSk{1} = AKE_eqS.mSk{2} /\
   AKE_find.mEexp{1} = AKE_eqS.mEexp{2} /\
   AKE_find.mStarted{1} = AKE_eqS.mStarted{2} /\
   AKE_find.mStarted{1} = AKE2toAKE3.mStarted{2} /\
   AKE_find.mCompleted{1} = AKE_eqS.mCompleted{2} /\
   AKE_find.mCompleted{1} = AKE2toAKE3.mCompleted{2} /\
   univ_map AKE_eqS.mEexp{2} /\ mSk_inv AKE_eqS.mSk{2} /\
  ! collision_eexp_eexp_op AKE_find.mEexp{1} /\ 
   AKE_find.t_idx{1} =  AKE2toAKE3.t_idx{2} /\ 
   inv_EPK AKE_eqS.mEexp{2} AKE2toAKE3.mEPK{2}  /\
  is_sub_map AKE2toAKE3.mCompleted{2} AKE2toAKE3.mStarted{2}  /\
  is_sub_map AKE2toAKE3.mEPK{2} AKE2toAKE3.mStarted{2}  /\
  is_sub_map AKE2toAKE3.mStarted{2} AKE2toAKE3.mEPK{2} /\
  is_sub_map AKE2toAKE3.mKeyRev{2} AKE2toAKE3.mCompleted{2} /\
  is_dom AKE2toAKE3.sKeyRev{2} AKE2toAKE3.mKeyRev{2} /\
inv_KeyRev AKE2toAKE3.mKeyRev{2} AKE2toAKE3.evs{2} AKE2toAKE3.mStarted{2}
  AKE2toAKE3.mCompleted{2} AKE_eqS.mEexp{2}
).
call AKE_find_eqS_choose; skip; progress.
apply tr_sim_empty.
rewrite /inv_KeyRev; smt.
 if{1}.
 rcondt{2} 1 => //.
 rcondt{2} 5 => //.
 progress; wp; skip => //; progress.
 generalize H12; rewrite /compute_sid H13 /= H3 //.
 by apply H6; generalize H9; rewrite /in_dom.
 rnd{1}; wp.

call AKE_find_eqS_guess; wp; rnd; wp; skip; progress.
  by rewrite /compute_sid H13 H3 //=; apply H6; generalize H9; rewrite /in_dom.
  smt.
  by rewrite mem_def.
  by generalize H44; apply tr_sim_fresh_op.
  if{2}.
  rcondf{2} 5 => //.
  intros => ?; wp; skip; progress => //.
  generalize H10; rewrite /compute_sid H13 /= H3 //.
    by apply H6; generalize H11; rewrite /in_dom.
    smt.
  wp; progress; rnd{1}; skip; progress; smt.
  wp; progress; rnd{1}; skip; progress.
  smt.
  generalize H10 H15 H17.
  rewrite /in_dom.
  case (AKE2toAKE3.mCompleted{2}.[AKE2toAKE3.t_idx{2}] = None) => //= h.
  cut: ! AKE2toAKE3.mStarted{2}.[AKE2toAKE3.t_idx{2}] = None.
  cut: in_dom AKE2toAKE3.t_idx{2} AKE2toAKE3.mStarted{2}.
   by apply H4; rewrite /in_dom.
   by rewrite /in_dom.
  case (AKE2toAKE3.mStarted{2}.[AKE2toAKE3.t_idx{2}] = None) => //=.
  smt.
  generalize H17.
  by apply tr_sim_fresh_op => //.
qed.

local lemma  Pr5_aux &m :
Pr[AKE_find(A).main()@ &m :
(AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\
mem
(get_string_from_id AKE_find.t_idx AKE_find.mStarted 
  AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) 
AKE_find.sH2 /\
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs) ] <=
Pr[AKE_eqS(AKE2toAKE3).main() @ &m :
(in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs)].
proof strict.
 equiv_deno AKE_find_eqS => //.
save.

local lemma Pr_sofar3 : forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
1%r/2%r + 
Pr[AKE_eqS(AKE2toAKE3).main() @ &m :
(in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs)].
proof strict. 
 intros => &m.
 apply (Real.Trans _
(1%r/2%r + 
Pr[AKE_find(A).main() @ &m : 
AKE_find.test <> None /\ 
in_dom AKE_find.t_idx AKE_find.mCompleted /\ 
mem
(get_string_from_id AKE_find.t_idx AKE_find.mStarted 
  AKE_find.mCompleted AKE_find.mEexp AKE_find.mSk) 
AKE_find.sH2 /\
fresh_op (compute_sid AKE_find.mStarted AKE_find.mEexp AKE_find.mCompleted AKE_find.t_idx) AKE_find.evs]) _).
apply (Pr_sofar2 &m).
apply real_le_plus.
smt.
apply (Pr5_aux &m).
save.

lemma Pr_sofar3' : exists (B <: Adv3), forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
1%r/2%r + 
Pr[AKE_eqS(B).main() @ &m :
(in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs)].
proof strict. 
 exists AKE2toAKE3.
 apply Pr_sofar3.
save.

end section.

lemma Pr5 : 
forall (A <: Adv2{AKE_EexpRev, AKE_eqS}),
(forall (O <: AKE_Oracles2{A}),
  islossless O.eexpRev =>
  islossless O.h2_a =>
  islossless O.init1 =>
  islossless O.init2 =>
  islossless O.resp =>
  islossless O.staticRev => islossless O.sessionRev => islossless A(O).choose) =>
(forall (O <: AKE_Oracles2{A}),
  islossless O.eexpRev =>
  islossless O.h2_a =>
  islossless O.init1 =>
  islossless O.init2 =>
  islossless O.resp =>
  islossless O.staticRev => islossless O.sessionRev => islossless A(O).guess)
=> exists (B <: Adv3), 
forall &m,
Pr[AKE_EexpRev(A).main() @ &m : res /\ test_fresh AKE_EexpRev.test AKE_EexpRev.evs
                    /\ ! collision_eexp_eexp(AKE_EexpRev.mEexp) 
                    /\ ! collision_eexp_rcvd(AKE_EexpRev.evs)] <=
1%r/2%r + 
Pr[AKE_eqS(B).main() @ &m :
(in_dom AKE_eqS.test_sidx AKE_eqS.mCompleted /\
List.mem
(get_string_from_id AKE_eqS.test_sidx AKE_eqS.mStarted 
  AKE_eqS.mCompleted AKE_eqS.mEexp AKE_eqS.mSk) 
(AKE_eqS.h2_queries) /\
fresh_op (compute_sid AKE_eqS.mStarted AKE_eqS.mEexp AKE_eqS.mCompleted AKE_eqS.test_sidx) AKE_eqS.evs)].
proof strict.
 intros => A hllc hllcg.
 by apply (Pr_sofar3' A _ _ ) => //.
save.