(* Reflexivity of a random procedure via dcoupl rnd (default identity
   bijection).                                                         *)
require import AllCore Distr DBool.

module M = {
  proc f() : bool = { var x : bool; x <$ {0,1}; return x; }
}.

lemma refl_rand : equiv[ M.f ~ M.f : true ==> ={res} ].
proof.
proc. delay.
dcoupl wp. dcoupl rnd.
move=> &1 &2 _. smt(dbool_ll supp_dbool).
qed.
