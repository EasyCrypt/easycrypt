module type T = { proc f() : unit}.
module A = { proc f() : unit = { } }.
module B = { proc f() : unit = { } }.
module F (A:T, B:T) = { 
  proc f () : unit = {
     A.f(); B.f();
  }
}.

module FA = F(A).
module FAB = FA(B).

require import Real.
lemma foo : bd_hoare [FAB.f : true ==> true] = 1%r.
proc.
admit.
save.