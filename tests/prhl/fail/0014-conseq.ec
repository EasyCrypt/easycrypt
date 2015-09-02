module M = { 
  proc f() : unit = {}
}.

lemma foo : hoare [M.f : true ==> false].
proof -strict.
  conseq [-frame] ( _: false ==> false).
  smt.
  smt.
  admit.
qed.