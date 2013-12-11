module M = { 
  proc f (x:int) : int = { return x; }
}.

equiv foo1 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}.
proof.
 conseq (_ : x{1} = x{1} ==> res{1} = res{1}).
 conseq (_ : _ ==> true /\ res{1} = res{1}).
 conseq (_ : ==> true /\ res{1} = res{1}).
 conseq (_ : x{1} = x{1} ==> _).
 conseq (_ : true /\ x{1} = x{1}).
 proc;skip;intros &m1 &m2 h;apply h.
save.

equiv foo2 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}.
proof.
 proc.
 conseq (_ : x{1} = x{1} ==> x{1} = x{1}).
 conseq (_ : _ ==> true /\ x{1} = x{1}).
 conseq (_ : ==> true /\ x{1} = x{1}).
 conseq (_ : x{1} = x{1} ==> _).
 conseq (_ : true /\ x{1} = x{1}).
 skip;intros &m1 &m2 h;apply h.
save.
