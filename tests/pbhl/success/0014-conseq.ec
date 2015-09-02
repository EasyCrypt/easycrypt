require import Int.
require import Real.
require import Distr.
require import Bool.

module M = { 
  
  proc f() : bool = { 
    var x : bool;
    x = $Dbool.dbool;
    return x;
  }
}.

lemma foo : phoare [M.f : false ==> res] = (1%r/2%r).
  conseq [-frame] ( _: true ==> res=true).
  smt.
  smt.
  proc.
  rnd (1%r/2%r) (fun (x), x). 
  skip.
  smt.
qed.

module M2 = { 
  proc f() : int = { 
    return 2;
  }
}.

lemma foo2 : phoare [M2.f : true ==> false] <= 1%r.
  conseq [-frame] ( _: true ==> res<=2).
  smt.
  smt.
  proc.
  pr_bounded. 
  smt.
qed.

lemma foo3 : phoare [M2.f : true ==> true] >= (1%r/2%r).
  conseq [-frame] ( _: true ==> res=2).
  smt.
  smt.
  proc.
  admit.
(* 
  FIXME: either I extend the conseq tactic with an 
  optional parameter to change also the bound... 
  or the skip tactics accepts lower-bounded judgments 
  and requires bhs_bd <= 1 as subgoal.
*)
qed.

lemma bug_15920 : phoare [M2.f : true ==> false] <= 1%r.
  conseq [-frame] ( _: true ==> _).
  smt.
  proc.
  pr_bounded. 
  smt.
qed.
