module M = { 
  fun f () : unit = { }
}.

equiv foo : M.f ~ M.f : true ==> true.
proof.
  fun.
  skip.
  intros _ _ h;assumption h.
save.
