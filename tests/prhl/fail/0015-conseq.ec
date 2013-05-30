module M = { 
  fun f() : unit = {}
}.

lemma foo : hoare [M.f : true ==> false]
proof.
  conseq ( _: true ==> true).
  trivial.
  trivial.
  admit.
save.