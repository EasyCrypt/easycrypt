module M = { 
  proc f () : unit = { }
}.

lemma foo : hoare [M.f : true ==> true].
proof.
 proc.
 skip.
 intros _ h.
 assumption h.
qed.

