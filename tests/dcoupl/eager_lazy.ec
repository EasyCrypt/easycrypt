(* Eager/Lazy sampling (paper, Examples): the eager sample of xh is
   delayed through the adversary. The call rule and the Abs rule do
   their part; the oracle premise is left admitted: closing it needs
   the delay context to become conditioned on x after the first query
   (a stack-conseq rule that is not in the logic yet).                *)
require import AllCore Distr.

type t.
op d : t distr.
axiom d_ll : is_lossless d.

module V = { var x : t option  var xh : t }.

module type O = { proc get() : t option }.
module type Adv(O : O) = { proc run() : bool }.

module OE : O = {
  proc get() : t option = {
    if (V.x = None) { V.x <- Some V.xh; }
    return V.x;
  }
}.

module OL : O = {
  proc get() : t option = {
    var v : t;
    if (V.x = None) { v <$ d; V.x <- Some v; }
    return V.x;
  }
}.

module GE(A : Adv) = {
  proc main() : bool = {
    var r : bool;
    V.x <- None; V.xh <$ d; r <@ A(OE).run();
    return r;
  }
}.

module GL(A : Adv) = {
  proc main() : bool = {
    var r : bool;
    V.x <- None; r <@ A(OL).run();
    return r;
  }
}.

(* Stated with the sample of xh still delayed at the end. *)
lemma eager_lazy (A <: Adv {-V}) :
  dcoupl[ , GE(A).main , V.xh <$ d; ~ , GL(A).main , : ={glob A} ==> ={res} ].
proof.
proc.
dcoupl seq 2 1 (={glob A, V.x}) with (V.xh <$ d; ~ ).
- dcoupl seq 1 1 (={glob A, V.x}) with ( ~ ).
  + dcoupl asgn {1}. dcoupl asgn {2}. dcoupl skip. smt().
  + dcoupl delay {1}. smt().
- (* { theta | xh <$ d x eps } r <@ A(OE).run() ~ r <@ A(OL).run() { ={res} | xh <$ d x eps } *)
  dcoupl call (_: ={V.x}).
  + (* { ={V.x} /\ ={glob A} | xh <$ d x eps } OE.get ~ OL.get { ... | xh <$ d x eps } *)
    admit.
  + dcoupl skip. smt().
qed.
