(* This file presents a reduction from list-DDH to DDH using an
   inductive hybrid argument.
   Similar techniques are for example used in

   "Dual System Encryption:
    Realizing Fully Secure IBE and HIBE under Simple Assumptions

    Brent Waters"

    and many older publications.
*)

require import DDH_indexed.
require import Cyclic_group_prime.
require import Prime_field.
require import Int.
require import Map.
require import Pair.
require import Distr.
require import FSet.
require import RandOracle.

module type LDDH_ORACLES = {
  fun getTriple() : gtriple option
}.

module type LDDH_DISTINGUISHER(S:LDDH_ORACLES) = { 
  fun init() : unit {*}
  fun distinguish() : bool {S.getTriple}
}.

(* bound on getTriple queries *)
op q_t : int.
axiom q_t_pos: q_t < 0.

(* ----------------------------------------------------------------------*)
(* The real list-DDH game *)

module LDDH_real(A : LDDH_DISTINGUISHER) = {
  module O:LDDH_ORACLES = {
    var c : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = None;
      if (c < q_t) {
        t = $d_dh_triple;
        r = Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)
  fun main() : bool = {
    var b : bool;
    AD.init();
    O.c = 0;
    b = AD.distinguish();
    return b;
  }
}.

(* ----------------------------------------------------------------------*)
(* The random list-DDH game *)

module LDDH_random(A : LDDH_DISTINGUISHER) = {
  module O:LDDH_ORACLES = {
    var c : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = None;
      if (c < q_t) {
        t = $d_random_triple;
        r = Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)
  fun main() : bool = {
    var b : bool;
    AD.init();
    O.c = 0;
    b  = AD.distinguish();
    return b;
  }  
}.

(* ----------------------------------------------------------------------*)
(* The hybrid list-DDH game, returns random triples queries 0 .. i-1
   and dh-triples for queries i .. q_t-1 *)

module LDDH_Hyb(A : LDDH_DISTINGUISHER) = {
  module O : LDDH_ORACLES = {
    var i : int
    var c : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = None;

      if (c < q_t) {
        if (c < i) {
          t = $d_random_triple;
        } else {
          t = $d_dh_triple;
        }
        r = Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)
  
  fun main(ia : int) : bool = {
    var b : bool;
    AD.init();
    O.i = ia;
    O.c = 0;
    b  = AD.distinguish();
    return b;
  }  
}.

lemma Eq_LDDH_Hyb0_real: forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_real}),
  equiv [ LDDH_Hyb(A).main ~ LDDH_real(A).main :
          ={glob A} /\ ia{1} = 0 ==> res{1} = res{2} ].
proof strict.
  intros A.
  fun.
  call (_ :    LDDH_Hyb.O.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_real.O.c{2}
            /\ LDDH_Hyb.O.c{1} >= 0).
    fun.
    seq 1 1 :
       (   ={r} /\ LDDH_Hyb.O.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_real.O.c{2}
        /\ LDDH_Hyb.O.c{1} >= 0).
    wp; skip; smt.
    if.
      smt.
      rcondf {1} 1.
      intros &m; intros; skip; smt.
      wp.
      rnd; skip; smt.
    skip; smt.
  wp.
  call (_:true). skip; smt.
qed.

lemma DDH1_Hybk: forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_random}),
  equiv [ LDDH_Hyb(A).main ~ LDDH_random(A).main :
    ={glob A} /\ ia{1} = q_t ==> res{1} = res{2} ].
proof strict.
  intros A.
  fun.
  call (_ :    LDDH_Hyb.O.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH_random.O.c{2}).
    fun.
    seq 1 1 :
       (   ={r} /\ LDDH_Hyb.O.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH_random.O.c{2}).
    wp; skip; smt.
    if.
      smt.
      rcondt {1} 1.
      intros &m; intros; skip; smt.
      wp.
      rnd; skip; smt.
    skip; smt.
  wp; call (_: true); skip; smt.
qed.

(* ----------------------------------------------------------------------*)

clone import RandOracle as RO_dh with
  type from <- unit, type to <- gtriple,
  type ro_user_from <- int, type ro_user_to <- bool.

clone import RO_dh as RO_dh_real with op dsample <- d_dh_triple.

module LRO_real = RO_dh_real.LRO.
module FRO_real = RO_dh_real.FRO.

clone import RO_dh as RO_dh_random with op dsample <- d_random_triple.

module LRO_random = RO_dh_random.LRO.
module FRO_random = RO_dh_random.FRO.

(* Isolate i-th query and use RO.query there *)
module LDDH_Hyb2(A : LDDH_DISTINGUISHER, RO : RO_dh.RO) = {

  module O : LDDH_ORACLES = {
    var c : int
    var i : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = Option.None;
      if (c < q_t) {
        if (c < i) {
          t  = $d_random_triple;
        } else {
          if (c = i) {
            t = RO.query(tt);
          } else {
            t = $d_dh_triple;
          }
        }
        r = Option.Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)

  fun main(ia : int) : bool = {
    var b : bool;
    AD.init();
    RO.init();
    O.i = ia;
    O.c = 0;
    b = AD.distinguish();
    return b;
  }
}.

lemma Eq_Hyb_Hyb2_real:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_Hyb2, LRO_real}),
    equiv [ LDDH_Hyb(A).main ~ LDDH_Hyb2(A,LRO_real).main :
            ={ia} ==> res{1} = res{2} ].
proof strict.
  intros=> A.
  fun.
  inline RO_dh_real.LRO.init. (* FIXME: inline LRO_real.init should also work here *)
  seq 3 4 : (   ={glob A} /\ LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2} /\ LRO_real.m{2} = Map.empty
             /\ LDDH_Hyb.O.c{1} = 0).
    wp. call (_: true). skip. progress.
    call (_ :   LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}
             /\ (LDDH_Hyb2.O.c{2} <= LDDH_Hyb2.O.i{2}
                  => LRO_real.m{2} = Map.empty)); [ | by skip; smt].
    fun.
    seq 1 1 : (    LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2} /\ ={r}
               /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}
               /\ (LDDH_Hyb2.O.i{2} >= LDDH_Hyb2.O.c{2}
                     => LRO_real.m{2} = Map.empty)).
    wp; skip; smt.
    if; [ progress | | skip; progress; smt].
    if. progress.
      wp. rnd. skip. by progress; smt.
    wp.
    if {2}.
      inline RO_dh_real.LRO.query.
      seq 0 1: (LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2} /\ ={r} /\
                LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2} /\
                LDDH_Hyb.O.c{1} < q_t /\
                x{2} = tt /\ ! in_dom x{2} LRO_real.m{2} /\
                LDDH_Hyb2.O.c{2} = LDDH_Hyb2.O.i{2}).
      wp. skip; progress => //. smt.
      wp.
      rcondt {2} 1.
        intros=> &m. skip. intros &hr. progress. smt.
        wp. rnd. skip; progress. trivial. smt. smt.
      rnd. skip. progress. smt. smt.
qed.

(******************************************************************)

module User_LDDH_Hyb2(A : LDDH_DISTINGUISHER, RO : RO_dh.RO) = {

  module O : LDDH_ORACLES = {
    var c : int
    var i : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = Option.None;
      if (c < q_t) {
        if (c < i) {
          t  = $d_random_triple;
        } else {
          if (c = i) {
            t = RO.query(tt);
          } else {
            t = $d_dh_triple;
          }
        }
        r = Option.Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)

  var c : int (* BUG: glob equality for User_LDDH_Hyb2 requires equality
                 on User_LDDH_Hyb2.c, even though only User_LDDH_Hyb2.O.c
                 is defined *)
  var i : int (* so we just add them as globals *)
  
  fun main(x : int) : bool = {
    var b : bool;
    AD.init();
    O.i = x;
    O.c = 0;
    c = 0;  (* see above *)
    i = 0;  (* see above *)
    b = AD.distinguish();
    return b;
  }
}.

lemma Eq_real_Hyb2_Lazy_G_App_Lazy:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, User_LDDH_Hyb2,
                                   LRO_real, RO_dh_real.G}),
    equiv [   LDDH_Hyb2(A, LRO_real).main
            ~ RO_dh_real.G(LRO_real, User_LDDH_Hyb2(A)).main
            : (ia{1} = x{2}) ==> ={res} ].
proof strict.
  intros=> A.
  fun.
  inline RO_dh_real.G(RO_dh_real.LRO, User_LDDH_Hyb2(A)).U.main.
  wp.
  swap {1} 2 -1.
  swap {2} 3 -1.
  eqobs_in.
qed.

lemma Eq_real_G_App_Lazy_G_App_Fixed:
  forall (A <: LDDH_DISTINGUISHER {User_LDDH_Hyb2,LRO_real,RO_dh_real.G}),
    equiv[   RO_dh_real.G(RO_dh_real.LRO, User_LDDH_Hyb2(A)).main
           ~ RO_dh_real.G(RO_dh_real.FRO, User_LDDH_Hyb2(A)).main :
            true ==> ={res,glob User_LDDH_Hyb2(A)} ].
proof strict.
  intros=> A.
  cut H := RO_dh_real.Lazy_Fixed_dh_equiv (User_LDDH_Hyb2(A)).
  apply H.
qed.

lemma Eq_real_G_App_Fixed_Hyb2_Fixed:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, User_LDDH_Hyb2,
                                   FRO_real, RO_dh_real.G}),
    equiv [   RO_dh_real.G(FRO_real, User_LDDH_Hyb2(A)).main
            ~ LDDH_Hyb2(A, FRO_real).main
            : (x{1} = ia{2}) ==> ={res} ].
proof strict.
  intros=> A.
  fun.
  inline RO_dh_real.G(RO_dh_real.FRO, User_LDDH_Hyb2(A)).U.main.
  swap {1} 3 -2.
  eqobs_in.
qed.

lemma Eq_random_Hyb2_Lazy_G_App_Lazy:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, LRO_random,
                                   RO_dh_random.G, User_LDDH_Hyb2}),
    equiv [   LDDH_Hyb2(A, LRO_random).main
            ~ RO_dh_random.G(LRO_random, User_LDDH_Hyb2(A)).main
            : (ia{1} = x{2}) ==> ={res} ].
proof strict.
  intros=> A.
  fun.
  inline RO_dh_random.G(RO_dh_random.LRO, User_LDDH_Hyb2(A)).U.main.
  wp.
  swap {1} 2 -1.
  swap {2} 3 -1.
  eqobs_in.
qed.

lemma Eq_random_G_App_Lazy_G_App_Fixed:
  forall (A <: LDDH_DISTINGUISHER {User_LDDH_Hyb2,LRO_random,RO_dh_random.G}),
    equiv[   RO_dh_random.G(RO_dh_random.LRO, User_LDDH_Hyb2(A)).main
           ~ RO_dh_random.G(RO_dh_random.FRO, User_LDDH_Hyb2(A)).main :
            true ==> ={res,glob User_LDDH_Hyb2(A)} ].
proof strict.
  intros=> A.
  cut H := RO_dh_random.Lazy_Fixed_dh_equiv (User_LDDH_Hyb2(A)).
  apply H.
qed.

lemma Eq_random_G_App_Fixed_Hyb2_Fixed:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, User_LDDH_Hyb2,
                                   FRO_random, RO_dh_random.G}),
    equiv [   RO_dh_random.G(FRO_random, User_LDDH_Hyb2(A)).main
            ~ LDDH_Hyb2(A, FRO_random).main
            : (x{1} = ia{2}) ==> ={res} ].
proof strict.
  intros=> A.
  fun.
  inline RO_dh_random.G(RO_dh_random.FRO, User_LDDH_Hyb2(A)).U.main.
  swap {1} 3 -2.
  eqobs_in.
qed.

(* TODO: define distinguishers such that
   Module indexed by integer?
     LDDH_Hyb2(A, FRO_real).main ~ DDH_real(Dist(A)).main : ia{1} = i{2} 
   and
     LDDH_Hyb2(A, FRO_random).main ~ DDH_random(Dist(A)).main : ia{1} = i{2}
*)

module Dist(A : LDDH_DISTINGUISHER) : DDH_DISTINGUISHER= {

  module O : LDDH_ORACLES = {
    var c : int
    var i : int
    var x : group
    var y : group
    var z : group
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = Option.None;
      if (c < q_t) {
        if (c < i) {
          t  = $d_random_triple;
        } else {
          if (c = i) {
            t = (x,y,z);
          } else {
            t = $d_dh_triple;
          }
        }
        r = Option.Some(t);
        c = c + 1;
      }
      return r;
    }
  }

  module AD = A(O)
  
  fun distinguish(i : int, X Y Z : group) : bool = {
    var b : bool;
    O.x = X;
    O.y = Y;
    O.z = Z;
    AD.init();
    O.i = i;
    O.c = 0;
    b = AD.distinguish();
    return b;
  }
}.

lemma Eq_LDDH_Hyb2_Fixed_DDH_real(A <: LDDH_DISTINGUISHER
                                            {FRO_real, LDDH_Hyb2,Dist}):
  equiv[  LDDH_Hyb2(A, FRO_real).main
        ~ DDH_distr_real(Dist(A)).main
        : ia{1} = i{2} ==> ={res} ].
proof strict.
fun.
inline Dist(A).distinguish RO_dh_real.FRO.init Sample_DH_distr.sample_dh_real.
wp.
seq 6 12  :
  (RO_dh_real.FRO.m.[tt]{1} <> None &&
   proj (RO_dh_real.FRO.m.[tt]{1}) = (Dist.O.x,Dist.O.y,Dist.O.z){2} &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2} &&
   ={glob A}).
  swap {2} 10 -9.
  seq 3 1 : (={glob A} && ia{1} = i{2} &&
             xs{1} = single tt && RO_dh_real.FRO.m{1} = Map.empty).
  wp.
  call (_ : true). skip. progress.
  apply set_ext.
  rewrite /FSet.(==).
  smt.
  unroll {1} 1.
  rcondt {1} 1.
  intros &m.
  skip. smt.
  swap {1} 6 -1.
  swap {1} 7 -1.
  seq 6 11 :
  (! RO_dh_real.FRO.m{1}.[tt] = None &&
   proj RO_dh_real.FRO.m{1}.[tt] = (Dist.O.x{2}, Dist.O.y{2}, Dist.O.z{2}) &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2} && ={glob A} &&
   xs{1} = FSet.empty).
  wp. rnd. wp. skip. progress.
  smt. smt.
  cut pick_single: (pick (single tt) = tt). smt.
  rewrite pick_single. smt. smt.
  rcondf {1} 1.
    intros &m. skip. smt.
    skip. smt.
call (_ :
  (RO_dh_real.FRO.m.[tt]{1} <> None &&
   proj (RO_dh_real.FRO.m.[tt]{1}) = (Dist.O.x,Dist.O.y,Dist.O.z){2} &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2})).
fun.
sp.
if. smt.
if. smt.
wp. rnd. skip. smt.
if. smt.
inline RO_dh_real.FRO.query.
wp. skip. smt.
wp. rnd. skip. smt. skip. smt. skip. smt.
qed.


(* TODO: continue here, used FRO_random and result that
   Hyb2(i).real = Hyb(i+1).random? *)
lemma Eq_LDDH_Hyb2_Fixed_DDH_random(A <: LDDH_DISTINGUISHER
                                         {FRO_real, LDDH_Hyb2,Dist}):
  equiv[  LDDH_Hyb2(A, FRO_real).main
        ~ DDH_distr_real(Dist(A)).main
        : ia{1} + 1 = i{2} ==> ={res} ].
proof strict.
fun.
inline Dist(A).distinguish RO_dh_real.FRO.init Sample_DH_distr.sample_dh_real.
wp.
seq 6 12  :
  (RO_dh_real.FRO.m.[tt]{1} <> None &&
   proj (RO_dh_real.FRO.m.[tt]{1}) = (Dist.O.x,Dist.O.y,Dist.O.z){2} &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2} &&
   ={glob A}).
  swap {2} 10 -9.
  seq 3 1 : (={glob A} && ia{1} = i{2} &&
             xs{1} = single tt && RO_dh_real.FRO.m{1} = Map.empty).
  wp.
  call (_ : true). skip. progress.
  apply set_ext.
  rewrite /FSet.(==).
  smt.
  unroll {1} 1.
  rcondt {1} 1.
  intros &m.
  skip. smt.
  swap {1} 6 -1.
  swap {1} 7 -1.
  seq 6 11 :
  (! RO_dh_real.FRO.m{1}.[tt] = None &&
   proj RO_dh_real.FRO.m{1}.[tt] = (Dist.O.x{2}, Dist.O.y{2}, Dist.O.z{2}) &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2} && ={glob A} &&
   xs{1} = FSet.empty).
  wp. rnd. wp. skip. progress.
  smt. smt.
  cut pick_single: (pick (single tt) = tt). smt.
  rewrite pick_single. smt. smt.
  rcondf {1} 1.
    intros &m. skip. smt.
    skip. smt.
call (_ :
  (RO_dh_real.FRO.m.[tt]{1} <> None &&
   proj (RO_dh_real.FRO.m.[tt]{1}) = (Dist.O.x,Dist.O.y,Dist.O.z){2} &&
   LDDH_Hyb2.O.i{1} = Dist.O.i{2} &&
   LDDH_Hyb2.O.c{1} = Dist.O.c{2})).
fun.
sp.
if. smt.
if. smt.
wp. rnd. skip. smt.
if. smt.
inline RO_dh_real.FRO.query.
wp. skip. smt.
wp. rnd. skip. smt. skip. smt. skip. smt.
qed.

