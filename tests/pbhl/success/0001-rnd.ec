require import Logic.
require import Distr.
require import Bool.
require import Real.


module M = {
  fun f (y:bool) : bool = {
    var x : bool;
    x = $Dbool.dbool; 
    return x=y;
  }
}.

lemma test: bd_hoare [ M.f : true ==> res] [=] [1%r/2%r] 
proof.
fun.
rnd (1%r/2%r) (lambda (x:bool), x=y).
skip.
simplify.
(* trivial. *) (* some bug *)
intros &hr.
trivial.
save.

