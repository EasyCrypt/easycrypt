require import Real.

module type T = {
  proc f() : unit
}.

module M : T = {
  var x : bool

  proc f() : unit = { }
}.

module type F (O:T) = {
  proc g() : unit
}.

module P (A:F) = {
  var y : bool
  
  module G = A(M)

  proc main() : unit = { M.x = false; G.g(); }
}.

lemma hoareF (A <: F {M}) : hoare [P(A).main : P.y /\ !P.y ==> false].
proof -strict.
 exfalso.
 smt. 
qed. 

lemma hoareS (A <: F {M}) : hoare [P(A).main : P.y /\ !P.y ==> false].
proof -strict.
 proc.
 exfalso.
 smt. 
qed. 

lemma bdhoareF_eq (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] = 1%r.
proof -strict.
 exfalso.
 smt. 
qed. 

lemma bdhoareF_le (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] <= 1%r.
proof -strict.
 exfalso.
 smt. 
qed. 

lemma bdhoareF_ge (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] >= 1%r.
proof -strict.
 exfalso.
 smt. 
qed. 

lemma bdhoareS_eq (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] = 1%r.
proof -strict.
 proc.
 exfalso.
 smt. 
qed. 

lemma bdhoareS_le (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] <= 1%r.
proof -strict.
 proc.
 exfalso.
 smt. 
qed. 

lemma bdhoareS_ge (A <: F {M}) : phoare [P(A).main : P.y /\ !P.y ==> P.y] >= 1%r.
proof -strict.
 proc.
 exfalso.
 smt. 
qed. 

lemma equivF (A <: F {M}) : equiv [P(A).main ~ P(A).main : P.y{1} /\ !P.y{1} ==> P.y{1}].
proof -strict.
 exfalso.
 smt. 
qed. 

lemma equivS (A <: F {M}) : equiv [P(A).main ~ P(A).main : P.y{1} /\ !P.y{1} ==> P.y{1}].
proof -strict.
 proc.
 exfalso.
 smt. 
qed. 


