(* This file presents a reduction from list-DDH to DDH using an
   inductive hybrid argument.
   Similar techniques are for example used in

   "Dual System Encryption:
    Realizing Fully Secure IBE and HIBE under Simple Assumptions

    Brent Waters"

    and many older publications.
*)

require import DDH.
require import Cyclic_group_prime.
require import Prime_field.
require import Int.
require import Map.
require import Pair.
require import Distr.
require import RandOracle.

module type LDDH_ORACLES = {
  fun getTriple() : gtriple option
}.

module type LDDH_DISTINGUISHER(S:LDDH_ORACLES) = { 
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
    O.i = ia;
    O.c = 0;
    b  = AD.distinguish();
    return b;
  }  
}.

lemma Eq_LDDH_Hybrid0_real: forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_real}),
  equiv [ LDDH_Hyb(A).main ~ LDDH_real(A).main :
          ={glob A} /\ ia{1} = 0 ==> res{1} = res{2} ].
proof strict.
  admit. (*
  intros A.
  fun.
  call (_ :    LDDH_Hyb.O.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_real.O.c{2}
            /\ LDDH_Hyb.O.c{1} >= 0).
    fun.
    seq 1 1 :
       (   ={r} /\ LDDH_Hyb.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH0.O.c{2}
        /\ LDDH_Hyb.O.c{1} >= 0).
    wp; skip; smt.
    if.
      smt.
      rcondf {1} 1.
      intros &m; intros; skip; smt.
      wp.
      inline DH_distrs.sample_dh.
      wp.
      rnd; rnd; skip; smt.
    skip; smt.
  wp; skip; smt. *)
qed.

lemma DDH1_Hybridk: forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_random}),
  equiv [ LDDH_Hyb(A).main ~ LDDH_random(A).main :
    ={glob A} /\ ia{1} = q_t ==> res{1} = res{2} ].
proof strict.
  admit. (*
  intros A.
  fun.
  call (_ :    LDDH_Hyb.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH1.O.c{2}).
    fun.
    seq 1 1 :
       (   ={r} /\ LDDH_Hyb.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH1.O.c{2}).
    wp; skip; smt.
    if.
      smt.
      rcondt {1} 1.
      intros &m; intros; skip; smt.
      wp.
      inline DH_distrs.sample_random.
      wp.
      rnd; rnd; rnd; skip; smt.
    skip; smt.
  wp; skip; smt. *)
qed.

(* ----------------------------------------------------------------------*)
(* We exploit the equivalences between the lazy and fixed implementations
   of modules to perform code-movement (of the samplings) from the
   getTriple oracle to main *)

(* We now perform the following steps:
   1. Isolate the i-th query in DDH_Hyb to obtain DDH_Hyb1.
   2. Implement i-th query using Lazy_DH.query
   3. Express game as G functor application and swap Lazy_DH with Fixed_DH
   4. Express game as DDH0 functor application (sampling for i-th query is
      in main)
   5. Change to DDH1 functor application (distance bounded by ddh assumption)
   6. Express as G functor application using Fixed_DH_random.
   7. Exchange Fixed_DH_random with Lazy_DH_random.
   8. Show that we have DDH_Hyb1 where the i-th query is answered
      with random triple, i.e., DDH_Hyb with i - 1.
*)

clone import RandOracle as RO_dh with
  type from = unit, type to = gtriple.

clone import RandOracle as RO_dh_real with
  type from = unit, type to = gtriple, op dsample = d_dh_triple.

module LRO_real =  RO_dh_real.LRO.
module FRO_real =  RO_dh_real.FRO.

clone import RandOracle as RO_dh_random with
  type from = unit, type to = gtriple, op dsample = d_random_triple.

module LRO_random =  RO_dh_random.LRO.
module FRO_random =  RO_dh_random.FRO.


module LDDH_Hyb2(RO : RO_dh.RO, A : LDDH_DISTINGUISHER) = {
  module O : LDDH_ORACLES = {
    var c : int
    var i : int
    fun getTriple() : gtriple option = {
      var t : gtriple;
      var r : gtriple option;
      r = Option.None;

      if (c < q_t) {
        if (c < i) {
          t  = $d_dh_triple;
        } else {
          if (c = i) {
            t = RO.query(tt);
          } else {
            t = $d_random_triple;
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
    RO.init();
    O.i = ia;
    O.c = 0;
    b = AD.distinguish();
    return b;
  }
}.

lemma Hyb1Hyb2: forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb, LDDH_Hyb2, LRO_real}),
  equiv [ LDDH_Hyb(A).main ~ LDDH_Hyb2(LRO_real, A).main :
    ={glob A, ia} ==> res{1} = res{2} ].
proof strict.
  intros=> A.
  fun.
  inline LRO_real.init.
  seq 2 3 : (   ={glob A} /\ LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2} ).
    wp. skip. smt.
    call (_ :   LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}).
    fun.
    seq 1 1 : (    LDDH_Hyb.i{1} = LDDH_Hyb2.i{2} /\ ={r}
               /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}).
    wp; skip; smt.
    if. smt.
    if. smt.
      eqobs_in.
        fun. rnd; rnd; rnd. skip. smt.
    if {2}.
      admit.
    eqobs_in.
      fun. rnd; rnd; skip. smt.
    skip. smt.
  skip.
  smt.
save.

(* Isolate the i-th query and call DDH1 *)



(*
    1. forall A. LDDH_Hybrid(A)_0 = LDDH0(A) and
       forall A. LDDH_Hybrid(A)_{q_t} = LDDH1(A)

    2. forall A m m' i,
         0 <= i ==> i < q - 1 ==>
              |Pr[LDDH_Hybrid(A)_i @ m : res]  - Pr[LDDH_Hybrid(A)_{i+1} @ m : res]|
           <= |Pr[DDH0(S(A)) @ m' : res] - Pr[DDH1(S(A)) : res]|
*)



(* we now move the sampling for the i-th query from
   getTriple to Main which will allow us in the
   next step to express the Hybrid game
   DDH_Hyb2(A) equivalently as  DDH(Sim(A)). *)
