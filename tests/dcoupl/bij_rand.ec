(* Equivalence via a non-identity bijection: f samples b, g samples !b.
   The coupling uses the negation bijection.                          *)
require import AllCore Distr DBool.

module M = {
  proc f() : bool = { var x : bool; x <$ {0,1}; return x; }
  proc g() : bool = { var x : bool; x <$ {0,1}; return !x; }
}.

lemma bij_rand : equiv[ M.f ~ M.g : true ==> ={res} ].
proof.
proc. delay.
dcoupl rnd (fun b => !b) (fun b => !b).
move=> &1 &2 _. smt(supp_dbool dbool1E).
qed.
