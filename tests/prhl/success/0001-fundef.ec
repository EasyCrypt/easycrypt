module M = { 
  fun f (x:int) : int = { return x; }
}.

lemma foo : equiv [M.f ~ M.f : x{1}=x{2} ==> res{1}=res{2}]
proof.
 fun.
 skip.
 intros &m1 &m2 h.
 assumption h.
save.