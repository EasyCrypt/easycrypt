module M = { 
  fun f () : unit = { }
}.

lemma foo : hoare [M.f : true ==> true]
proof.
 fun.
 skip.
 intros _ h.
 assumption h.
save.

