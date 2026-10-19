(* call with an invariant on an abstract procedure (adversary): the
   stacks pass through the adversary unchanged and are carried into
   each oracle premise. The module restrictions must keep the
   adversary away from the variables the stacks read or write.       *)
require import AllCore Distr.

module type O = { proc o(x : int) : int }.
module type Adv(O : O) = { proc run() : bool }.

module M : O = {
  var a, b : int
  proc o(x : int) : int = { M.a <- M.a + x; return M.a; }
}.

module G(A : Adv) = {
  proc main() : bool = { var r : bool; M.a <- 0; r <@ A(M).run(); return r; }
}.

module G2(A : Adv) = {
  proc main() : int = {
    var r : bool;
    M.b <- 5; r <@ A(M).run(); M.b <- M.b + 1;
    return M.b;
  }
}.

(* Empty stacks. *)
lemma abs_call (A <: Adv {-M}) :
  equiv[ G(A).main ~ G(A).main : ={glob A} ==> ={res} ].
proof.
proc. delay.
dcoupl call (_: ={M.a}).
- (* oracle premise: { ={M.a} /\ ={x} | eps } M.o ~ M.o { ={M.a} /\ ={res} | eps } *)
  proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* A delayed assignment to M.b goes through the adversary (A cannot
   access M.b) and is consumed afterwards.                           *)
lemma abs_call_stacks (A <: Adv {-M}) :
  equiv[ G2(A).main ~ G2(A).main : ={glob A, M.a} ==> ={res} ].
proof.
proc. delay.
dcoupl seq 2 2 (={glob A, M.a}) with (M.b <- 5; ~ M.b <- 5;).
- dcoupl push 1.
  (* { ={glob A} | M.b <- 5 } r <@ A(M).run() ~ ... { theta | M.b <- 5 } *)
  dcoupl call (_: ={M.a}).
  + (* { ={M.a} /\ ={x} | M.b <- 5 } M.o ~ M.o { ={M.a} /\ ={res} | M.b <- 5 } *)
    proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
  + dcoupl skip. smt().
- dcoupl pop 1.
  dcoupl asgn {1}. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl asgn {2}.
  dcoupl skip. smt().
qed.

(* With empty continuations the default stacks of the specification are
   empty too: the pushed instruction is consumed before the call and
   nothing goes through the adversary. *)
lemma abs_call_consumed (A <: Adv {-M}) :
  equiv[ G(A).main ~ G(A).main : ={glob A} ==> ={res} ].
proof.
proc. delay.
dcoupl push 1.
dcoupl call (_: ={M.a}).
- proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
- dcoupl pop 1. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.

(* Error: the stacks go through an adversary that may access M.a,
   which they write. *)
lemma abs_call_dep (A <: Adv) :
  equiv[ G(A).main ~ G(A).main : ={glob A} ==> ={res} ].
proof.
proc. delay.
dcoupl seq 2 2 (true) with (M.a <- 0; ~ M.a <- 0;).
dcoupl push 1.
fail dcoupl call (_: true).
admit. admit.
qed.

(* Abs at F-level directly: the stacks must be unchanged. *)
lemma abs_flevel (A <: Adv {-M}) :
  dcoupl[ , A(M).run , ~ , A(M).run , : ={glob A, M.a} ==> ={res, M.a} ].
proof.
proc (={M.a}).
- smt().
- smt().
- proc. dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
qed.
