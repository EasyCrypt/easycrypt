module M = { 
  proc f () : unit = { }
}.

equiv foo : M.f ~ M.f : true ==> true.
proof -strict.
  proc.
  skip.
  intros=> _ _ h; exact h.
qed.
