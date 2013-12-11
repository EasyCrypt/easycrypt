module M = { 
  proc f() : unit = {}
}.

lemma foo : hoare [M.f : false ==> true].
proof.
  conseq ( _: true ==> false).
  admit.
save.
