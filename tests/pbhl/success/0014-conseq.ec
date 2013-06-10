require import Real.

module M = { 
  fun f() : unit = {}
}.

lemma foo : bd_hoare [M.f : false ==> true] = 1%r.
proof.
  conseq ( _: true ==> false).
  trivial.
  trivial.
  admit.
save.