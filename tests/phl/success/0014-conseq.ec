module M = { 
  proc f() : unit = {}
}.

lemma foo : hoare [M.f : false ==> true].
proof -strict.
  conseq ( _: true ==> false).
  admit.
qed.
