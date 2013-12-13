(* -------------------------------------------------------------------- *)
require import Distr.
require import Bool.
require import Real.

(* -------------------------------------------------------------------- *)
module M1 = {
  var x : bool

  fun main() : unit = {
    x = ${0,1};
  }
}.

module M2 = {
  var x : int

  fun main() : unit = {
    x = $[0..1];
  }
}.

(* -------------------------------------------------------------------- *)
lemma test : equiv [M1.main ~ M2.main : true ==> true].
proof.
  fun; rnd.
qed.
