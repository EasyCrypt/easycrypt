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

lemma test: bd_hoare [ M.f : true ==> res] = (1%r/2%r).
proof.
fun.
rnd (1%r/2%r) (lambda (x:bool), x=y).
skip.
trivial.
simplify.
intros &hr.
rewrite (Dbool.mu_def  (lambda (x : bool), x = y{hr})).
smt.
save.

module F = {
  var b1 : bool
  var b2 : bool
  fun f () : bool = {
    b1 = $Dbool.dbool;
    b2 = $Dbool.dbool;
    return b1;
  }
}.

lemma test2: bd_hoare [ F.f : true ==> res] = (1%r/2%r). proof.
fun.
rnd (1%r) (lambda (x:bool), true).
rnd (1%r/2%r) (lambda (x:bool), x).
skip.
trivial.
simplify.
rewrite (Dbool.mu_def  (lambda (x : bool), true)).
rewrite (Dbool.mu_def  (lambda (x : bool), x)).
split.
trivial.
intros H v H'.
split.
trivial.
trivial.
save.


