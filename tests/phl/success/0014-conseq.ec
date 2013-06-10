module M = { 
  fun f() : unit = {}
}.

lemma foo : hoare [M.f : false ==> true].
proof.
  conseq ( _: true ==> false).
  trivial.
  trivial.
  admit.
save.