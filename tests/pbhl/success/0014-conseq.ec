require import Int.
require import Real.
require import Distr.
require import Bool.


module M = { 
  
  fun f() : bool = { 
    var x : bool;
    x = $Dbool.dbool;
    return x;
  }
}.

lemma foo : bd_hoare [M.f : false ==> res] = (1%r/2%r)
proof.
  conseq ( _: true ==> res=true).
  trivial.
  trivial.
  fun.
  rnd (1%r/2%r) (lambda (x), x). 
  skip.
  trivial.
save.

module M2 = { 
  fun f() : int = { 
    return 2;
  }
}.


lemma foo2 : bd_hoare [M2.f : true ==> false] <= 1%r
proof.
  conseq ( _: true ==> res<=2).
  trivial.
  trivial.
  fun.
  pr_bounded. 
  trivial.
save.


lemma foo3 : bd_hoare [M2.f : true ==> true] >= (1%r/2%r)
proof.
  conseq ( _: true ==> res=2).
  trivial.
  trivial.
  fun.
  admit.
(* 
  FIXME: either I extend the conseq tactic with an 
  optional parameter to change also the bound... 
  or the skip tactics accepts lower-bounded judgments 
  and requires bhs_bd <= 1 as subgoal.
*)
save.



