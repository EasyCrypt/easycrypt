module M = { 
  proc f () : unit = { }
}.

equiv foo : M.f ~ M.f : true ==> true.
proof.
  proc.
  skip.
  intros _ _ h;assumption h.
qed.
