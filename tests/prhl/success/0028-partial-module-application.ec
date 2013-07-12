module type T = { fun f() : unit}.
module A = { fun f() : unit = { } }.
module B = { fun f() : unit = { } }.
module F (A:T, B:T) = { 
  fun f () : unit = {
     A.f(); B.f();
  }
}.

module FA = F(A).
module FAB = FA(B).

require import Real.
lemma foo : bd_hoare [FAB.f : true ==> true] = 1%r.
fun.
admit.
save.