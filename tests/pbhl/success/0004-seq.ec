require import Distr.
require import Bool.
require import Real.

module M = {
  var y : bool
  var x : bool
  fun f() : unit = {
    y = $Dbool.dbool;
    x = $Dbool.dbool;
  }
}.

lemma test : bd_hoare [M.f : true ==> M.x /\ M.y ] = (1%r/4%r).
proof.
 fun.
 seq 1 : (M.y) true (1%r/2%r) (1%r/2%r) (1%r/2%r) 0%r => //.
 rnd (lambda (x:bool),x=true).
 skip; smt.
 rnd (lambda (x:bool),x).
 skip.
 progress;try smt.
 hoare;rnd;skip;smt.
save.

module M2 = {
  var y : bool
  var x : bool
  fun f() : unit = {
    y = true;
    x = $Dbool.dbool;
  }
}.

lemma test2 : bd_hoare [M2.f : true ==> M2.x /\ M2.y ] <= (1%r/2%r).
proof.
 fun.
 seq 1 : (M2.y) true 1%r (1%r/2%r) 0%r 0%r=> //.
 rnd (lambda (x:bool),x=true).
 skip;progress;smt.
 hoare;wp;trivial.
save.


module M3 = {
  var y : bool
  var x : bool
  fun f() : unit = {
    x = $Dbool.dbool;
    y = true;
  }
}.

lemma test3 : bd_hoare [M3.f : true ==> M3.x /\ M3.y ] <= (1%r/2%r).
proof.
 fun.
 seq 1 : (M3.x) true (1%r/2%r) (1%r) (1%r/2%r) (0%r)=> //.
 rnd (lambda (x:bool),x=true);skip; smt.
 wp;hoare=> //.
save.



(* FAILING *)
(*
module M2 = {
  var y : bool
  var x : bool
  fun f() : unit = {
    y = true;
    x = $Dbool.dbool;
  }
}.

lemma foo : bd_hoare [M.f : true ==> M.x /\ M.y ] [<=] [1%r/2%r]
proof.
 fun.
 seq>> 1 : (M.y) (1%r/2%r).
*)

