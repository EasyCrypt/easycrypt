(* This file presents a reduction from list-DDH to DDH using an
   inductive hybrid argument.
   Similar techniques are for example used in

   "Dual System Encryption:
    Realizing Fully Secure IBE and HIBE under Simple Assumptions

    Brent Waters"

    and many older publications.
*)

require import DDH.
require import Int.
require import Distr.
require import FSet.
require import SmtMap.
require import PROM.

module type LDDH_ORACLES = {
  proc getTriple() : gtriple option
}.

module type LDDH_DISTINGUISHER (S : LDDH_ORACLES) = {
  proc distinguish() : bool { S.getTriple }
}.

(* bound on getTriple queries *)
op q_t        : int.
axiom q_t_pos : q_t < 0.

(* ----------------------------------------------------------------------*)
(* The real list-DDH game *)

module LDDH_real_O : LDDH_ORACLES = {
  var c : int

  proc getTriple() : gtriple option = {
    var t : gtriple;
    var r : gtriple option;

    r <- None;
    if (c < q_t) {
      t <$ d_dh_triple;
      r <- Some(t);
      c <- c + 1;
    }
    return r;
  }
}.

module LDDH_real (A : LDDH_DISTINGUISHER) = {

  module O = LDDH_real_O
  module AD = A(O)

  proc main () : bool = {
    var b : bool;

    O.c <- 0;
    b   <@ AD.distinguish();
    return b;
  }
}.

(* ----------------------------------------------------------------------*)
(* The random list-DDH game *)

module LDDH_random_O : LDDH_ORACLES = {
  var c : int

  proc getTriple() : gtriple option = {
    var t : gtriple;
    var r : gtriple option;

    r <- None;
    if (c < q_t) {
      t <$ d_random_triple;
      r <- Some(t);
      c <- c + 1;
    }
    return r;
  }
}.

module LDDH_random (A : LDDH_DISTINGUISHER) = {

  module O = LDDH_random_O
  module AD = A(O)

  proc main () : bool = {
    var b : bool;
    O.c <- 0;
    b   <@ AD.distinguish();
    return b;
  }
}.

(* ----------------------------------------------------------------------*)
(* The hybrid list-DDH game, returns random triples queries 0 .. i-1
   and dh-triples for queries i .. q_t-1 *)

module LDDH_Hyb_O : LDDH_ORACLES = {
  var i : int
  var c : int

  proc getTriple() : gtriple option = {
    var t : gtriple;
    var r : gtriple option;

    r <- None;
    if (c < q_t) {
      if (c < i) {
        t <$ d_random_triple;
      } else {
        t <$ d_dh_triple;
      }
      r <- Some(t);
      c <- c + 1;
    }
    return r;
  }
}.

module LDDH_Hyb (A : LDDH_DISTINGUISHER) = {

  module O = LDDH_Hyb_O
  module AD = A(O)

  proc main (ia : int) : bool = {
    var b : bool;

    O.i <- ia;
    O.c <- 0;
    b   <@ AD.distinguish();
    return b;
  }
}.

lemma Eq_LDDH_Hybrid0_real:
  forall (A <: LDDH_DISTINGUISHER {-LDDH_Hyb, -LDDH_Hyb_O, -LDDH_real, -LDDH_real_O}),
    equiv [ LDDH_Hyb(A).main ~ LDDH_real(A).main :
            ={glob A} /\ ia{1} = 0 ==> res{1} = res{2} ].
proof strict.
  move=> A.
  proc.
  call (_ :    LDDH_Hyb.O.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_real.O.c{2}
            /\ 0 <= LDDH_Hyb.O.c{1}).
    proc.
    seq 1 1 :
       (   ={r} /\ LDDH_Hyb.O.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_real.O.c{2}
        /\ 0 <= LDDH_Hyb.O.c{1}).
    wp; skip; smt.
    if.
      smt.
      rcondf {1} 1.
      move=> &m; skip; smt.
      wp. rnd; skip; smt.
    skip; smt.
  wp; skip; smt.
qed.

lemma DDH1_Hybridk:
  forall (A <: LDDH_DISTINGUISHER {-LDDH_Hyb, -LDDH_Hyb_O, -LDDH_random, -LDDH_random_O}),
    equiv [ LDDH_Hyb(A).main ~ LDDH_random(A).main :
            ={glob A} /\ ia{1} = q_t ==> res{1} = res{2} ].
proof strict.
  move=> A.
  proc.
  call (_ : LDDH_Hyb.O.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH_random.O.c{2}).
    proc.
    seq 1 1 : (={r} /\ LDDH_Hyb.O.i{1} = q_t /\ LDDH_Hyb.O.c{1} = LDDH_random.O.c{2}).
    wp; skip; smt.
    if.
      smt.
      rcondt {1} 1.
      move=> &m; skip; smt.
      wp.
      rnd; skip; smt.
    skip; smt.
  wp; skip; smt.
qed.

(* ----------------------------------------------------------------------*)
(* We exploit the equivalences between the lazy and fixed implementations
   of modules to perform code-movement (of the samplings) from the
   getTriple oracle to main *)

(* We now perform the following steps:
   1. Isolate the i-th query in DDH_Hyb to obtain DDH_Hyb2.
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

clone import FullRO as RO_dh with
  type in_t <- unit, type out_t <- gtriple.

clone import RO_dh as RO_dh_real with op dout <- (fun _ => d_dh_triple).

module LRO_real =  RO_dh_real.LRO.
module FRO_real =  RO_dh_real.FRO.

clone import RO_dh as RO_dh_random with op dout <- (fun _ => d_random_triple).

module LRO_random =  RO_dh_random.LRO.
module FRO_random =  RO_dh_random.FRO.

(* Isolate i-th query and use RO.query there *)
module LDDH_Hyb2_O (RO : RO_dh.RO) : LDDH_ORACLES = {
  var c : int
  var i : int

  proc getTriple() : gtriple option = {
    var t : gtriple;
    var r : gtriple option;

    r <- None;
    if (c < q_t) {
      if (c < i) {
        t <$ d_random_triple;
      } else {
        if (c = i) {
          t <@ RO.get();
        } else {
          t <$ d_dh_triple;
        }
      }
      r <- Some(t);
      c <- c + 1;
    }
    return r;
  }
}.

module LDDH_Hyb2 (RO : RO_dh.RO, A : LDDH_DISTINGUISHER) = {

  module O = LDDH_Hyb2_O(RO)
  module AD = A(O)

  proc main (ia : int) : bool = {
    var b : bool;

    RO.init();
    O.i <- ia;
    O.c <- 0;
    b   <@ AD.distinguish();
    return b;
  }
}.

lemma Eq_Hyb_Hyb2:
  forall (A <: LDDH_DISTINGUISHER {-LDDH_Hyb, -LDDH_Hyb2, -LRO_real,
                                   -LDDH_Hyb_O, -LDDH_Hyb2_O}),
    equiv [ LDDH_Hyb(A).main ~ LDDH_Hyb2(LRO_real, A).main :
            ={glob A, ia} ==> res{1} = res{2} ].
proof strict.
  move=> A.
  proc.
  inline LRO_real.init.
  seq 2 3 : (   ={glob A} /\ LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2} /\ RO_dh_real.RO.m{2} = empty
             /\ LDDH_Hyb.O.c{1} = 0).
    wp. skip. smt.
    call (_ :   LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2}
             /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}
             /\ (LDDH_Hyb2.O.c{2} <= LDDH_Hyb2.O.i{2}
                  => RO_dh_real.RO.m{2} = empty)); [ | by skip; smt].
    proc.
    seq 1 1 : (    LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2} /\ ={r}
               /\ LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2}
               /\ (LDDH_Hyb2.O.c{2} <= LDDH_Hyb2.O.i{2}
                     => RO_dh_real.RO.m{2} = empty)).
    wp; skip; smt.
    if; [ progress | | skip; progress; smt].
    if. progress.
      wp. rnd. skip. by progress; smt.
    wp.
    if {2}.
      inline RO_dh_real.LRO.get.
      seq 0 1: (LDDH_Hyb.O.i{1} = LDDH_Hyb2.O.i{2} /\ ={r} /\
                LDDH_Hyb.O.c{1} = LDDH_Hyb2.O.c{2} /\
                LDDH_Hyb.O.c{1} < q_t /\
                x{2} = tt /\ (x \notin RO_dh_real.RO.m){2} /\
                LDDH_Hyb2.O.c{2} = LDDH_Hyb2.O.i{2}).
      wp. skip; progress => //. smt.
      (*
      wp.
      *)
      rcondt {2} 2.
        by auto; auto => />.
        by auto => />; smt.
        (*
        move=> &m. skip. move=> &hr. progress. smt.
        wp. rnd. skip; progress. trivial. smt. smt.
        *)
      rnd. skip. progress. smt. (* smt. *)
qed.

(* INCOMPLETE

(******************************************************************)
(** We show that for the real DH oracle, LDDH_Hyb2 can be expressed
    as DDH_real(Sim(A)). *)

module Arg_LDDH_Hyb2(A : LDDH_DISTINGUISHER, RO : RO_dh.RO) = {

  module O = LDDH_Hyb2_O(RO)
  module AD = A(O)

  fun f(ia : int) : bool = {
    var b : bool;
    O.i = ia;
    O.c = 0;
    b = AD.distinguish();
    return b;
  }
}.

lemma Eq_real_Hyb2_G_App_Lazy:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, LRO_real,
                                   RO_dh_real.G}),
    equiv [   LDDH_Hyb2(LRO_real, A).main
            ~ RO_dh_real.G(LRO_real, Arg_LDDH_Hyb2(A)).main :
            ={glob A, ia} ==> ={res} ].

lemma Eq_real_G_App_Lazy_Fixed:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, LRO_real,
                                   RO_dh_real.G}),
    equiv [   RO_dh_real.G(LRO_real, Arg_LDDH_Hyb2(A)).main
            ~ RO_dh_real.G(FRO_real, Arg_LDDH_Hyb2(A)).main
            ={glob A, ia} ==> ={res} ].

lemma Eq_real_G_App_Hyb2_Fixed:
  forall (A <: LDDH_DISTINGUISHER {LDDH_Hyb2, LRO_real,
                                   RO_dh_real.G}),
    equiv [   RO_dh_real.G(FRO_real, Arg_LDDH_Hyb2(A)).main
            ~ LDDH_Hyb2(FRO_real, A).main :
            ={glob A, ia} ==> ={res} ].

(* works for both real and random *)
module Sim_LDDH_Hyb2 = {}.

lemma Eq_real_Hyb2_fixed_DDH:

(******************************************************************)
(** We show that for the random DH oracle, LDDH_Hyb2 can be expressed
    as DDH_random(Sim(A)). *)

lemma Eq_random_Hyb2_G_App_Lazy:

lemma Eq_random_G_App_Lazy_Fixed:

lemma Eq_random_G_App_Hyb2_Fixed

lemma Eq_random_Hyb2_fixed_DDH:

(******************************************************************)
(** We now bound the probability using induction. *)

*)
