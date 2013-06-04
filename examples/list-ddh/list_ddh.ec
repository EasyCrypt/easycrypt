(* This file presents a reduction from list-DDH to DDH using an
   inductive hybrid argument.
   Similar techniques are for example used in

   "Dual System Encryption:
    Realizing Fully Secure IBE and HIBE under Simple Assumptions

    Brent Waters"

    and many older publications.
*)

require import Option.
require import DDH.
require import Cyclic_group_prime.
require import Int.

module type LDDH_ORACLES = {
  fun getTriple() : (group * group * group) option
}.

module type LDDH_DISTINGUISHER(S:LDDH_ORACLES) = { 
  fun dist() : bool {S.getTriple}
}.

op q_t : int.

axiom q_t_pos: q_t > 0.

(* ----------------------------------------------------------------------*)
(* The real list-DDH game *)

module LDDH0(A : LDDH_DISTINGUISHER) = {
  module O:LDDH_ORACLES = {
    var c : int
    fun getTriple() : (group * group * group) option = {
      var t : (group * group * group);
      var r : (group * group * group) option;
      r = None;

      if (c < q_t) {
        c = c + 1;
        t := DH_distrs.sample_dh();
        r = Some(t);
      }
      return r;
    }
  }

  module AD = A(O)
  fun main() : bool = {
    var b : bool;
    O.c = 0;
    b := AD.dist();
    return b;
  }
}.


(* ----------------------------------------------------------------------*)
(* The random list-DDH game *)

module LDDH1(A : LDDH_DISTINGUISHER) = {
  module O:LDDH_ORACLES = {
    var c : int
    fun getTriple() : (group * group * group) option = {
      var t : (group * group * group);
      var r : (group * group * group) option;
      r = None;
      if (c < q_t) {
        c = c + 1;
        t := DH_distrs.sample_random();
        r = Some(t);
      }
      return r;
    }
  }

  module AD = A(O)
  fun main() : bool = {
    var b : bool;
    O.c = 0;
    b := AD.dist();
    return b;
  }  
}.


(* ----------------------------------------------------------------------*)
(* The hybrid list-DDH game, returns random triples queries 0 .. i-1
   and dh-triples for queries i .. q_t-1 *)

module LDDH_Hyb(A : LDDH_DISTINGUISHER) = {
  var i : int
  module O : LDDH_ORACLES = {
    var c : int
    fun getTriple() : (group * group * group) option = {
      var t : (group * group * group);
      var r : (group * group * group) option;
      r = None;

      if (c < q_t) {
        if (c < i) {
          t  := DH_distrs.sample_random();
        } else {
          t := DH_distrs.sample_dh();
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
    i = ia;
    O.c = 0;
    b := AD.dist();
    return b;
  }  
}.


lemma DDH0_Hybrid0: forall (A <: LDDH_DISTINGUISHER),
  equiv [ LDDH_Hyb(A).main ~ LDDH0(A).main :
     ((glob A){1} = (glob A){2}) /\ ia{1} = 0 ==> res{1} = res{2} ]
proof.
  intros A.
  fun.
  (* BUG1: This should complain about undefined variable, there is no LDDH_Hyb.0.c{2}  *)
  (* app 2 1 : ((glob A){1} = (glob A){2} /\ LDDH_Hyb.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH_Hyb.O.c{2}). *)
  app 2 1 :
    ((glob A){1} = (glob A){2} /\ LDDH_Hyb.i{1} = 0 /\ LDDH_Hyb.O.c{1} = LDDH0.O.c{2}).
  wp.
  skip.
  trivial.
  (* BUG2: unknown symbol: <top>.LDDH_Hyb./getTriple => indeed, there is only LDDH_Hyb.O.getTriple *)
  call ((glob A){1} = (glob A){2} && LDDH_Hyb.i{1} = 0)
       (res{1} = res{2} && LDDH_Hyb.i{1} = 0).

(* OLD
lemma DDH0_Hybrid0: forall (A <: LDDH_DISTINGUISHER),
  equiv [ LDDH_Hybrid(A).main ~ LDDH1(A).main : i{1} = q_t ==> res{1} = res{2} ]
proof.


call ((!mem F2.xs RO.logA){2} /\ h{1} = h{2} /\ (glob A){1} = (glob A){2} /\
         RO.logA{1} = RO.logA{2} /\ eq_except RO.mH{1} RO.mH{2} F2.xs{2})
       ( (!mem F2.xs RO.logA){2} => res{1} = res{2} ).
    fun (mem F2.xs RO.logA)
        (RO.logA{1} = RO.logA{2} /\ eq_except RO.mH{1} RO.mH{2} F2.xs{2}) true;

try (trivial).
      apply Hlossless.  
      fun; inline RO.hash;wp;rnd;wp;skip;simplify.
      intros &m1 &m2 H.
      elim H;clear H;intros H H1.
      elim H1;clear H1;intros H1 H2.
      elim H2;clear H2;intros H2 H3.
      elim H3;clear H3;intros H3 H4.
      intros rL rR H5.
      rewrite H1.
*)

(*
    1. forall A. LDDH_Hybrid(A)_0 = LDDH0(A) and
       forall A. LDDH_Hybrid(A)_{q_t} = LDDH1(A)

    2. forall A m m' i,
         0 <= i ==> i < q - 1 ==>
              |Pr[LDDH_Hybrid(A)_i @ m : res]  - Pr[LDDH_Hybrid(A)_{i+1} @ m : res]|
           <= |Pr[DDH0(S(A)) @ m' : res] - Pr[DDH1(S(A)) : res]|
*)


