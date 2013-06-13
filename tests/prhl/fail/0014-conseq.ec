module M = { 
  fun f() : unit = {}
}.

lemma foo : hoare [M.f : true ==> false].
proof.
  conseq ( _: false ==> false).
  trivial.
  trivial.
  admit.
save.