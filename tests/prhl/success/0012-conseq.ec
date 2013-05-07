module M = { 
  fun f (x:int) : int = { return x; }
}.

equiv foo1 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}
proof.
 conseq (_ : x{1} = x{1} ==> res{1} = res{1}).
 intros &m1 &m2 h;apply h.
 intros &m1 &m2 h;apply h.
 conseq (_ : _ ==> true /\ res{1} = res{1}).
 intros &m1 &m2 h;apply h.
 conseq (_ : ==> true /\ res{1} = res{1}).
 intros &m1 &m2 h;apply h.
 conseq (_ : x{1} = x{1} ==> _).
 intros &m1 &m2 h;apply h.
 conseq (_ : true /\ x{1} = x{1}).
 intros &m1 &m2 h;apply h.
 fun;skip;intros &m1 &m2 h;apply h.
save.

equiv foo2 : M.f ~ M.f : x{1} = x{1} ==> res{1} = res{1}
proof.
 fun.
 conseq (_ : x{1} = x{1} ==> x{1} = x{1}).
 intros &m1 &m2 h;apply h.
 intros &m1 &m2 h;apply h.
 conseq (_ : _ ==> true /\ x{1} = x{1}).
 intros &m1 &m2 h;apply h.
 conseq (_ : ==> true /\ x{1} = x{1}).
 intros &m1 &m2 h;apply h.
 conseq (_ : x{1} = x{1} ==> _).
 intros &m1 &m2 h;apply h.
 conseq (_ : true /\ x{1} = x{1}).
 intros &m1 &m2 h;apply h.
 skip;intros &m1 &m2 h;apply h.
save.
