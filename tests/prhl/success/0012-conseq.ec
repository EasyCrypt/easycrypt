module M = { 
  proc f (x:int) : int = { return x; }
}.

equiv foo1 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}.
proof -strict.
 conseq [-frame] (_ : x{1} = x{1} ==> res{1} = res{1}).
 conseq [-frame] (_ : _ ==> true /\ res{1} = res{1}).
 conseq [-frame] (_ : ==> true /\ res{1} = res{1}).
 conseq [-frame] (_ : x{1} = x{1} ==> _).
 conseq [-frame] (_ : true /\ x{1} = x{1}).
 proc;skip;intros &m1 &m2 h;apply h.
qed.

equiv foo2 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}.
proof -strict.
 proc.
 conseq [-frame] (_ : x{1} = x{1} ==> x{1} = x{1}).
 conseq [-frame] (_ : _ ==> true /\ x{1} = x{1}).
 conseq [-frame] (_ : ==> true /\ x{1} = x{1}).
 conseq [-frame] (_ : x{1} = x{1} ==> _).
 conseq [-frame] (_ : true /\ x{1} = x{1}).
 skip;intros &m1 &m2 h;apply h.
qed.
