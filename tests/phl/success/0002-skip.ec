module M = { 
  proc f () : unit = { }
}.

lemma foo : hoare [M.f : true ==> true].
proof -strict.
 proc.
 skip.
 intros _ h.
 exact h.
qed.

