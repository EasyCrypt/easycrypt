module M = { 
  proc f (x:int) : int = { return x; }
}.

lemma foo : hoare [M.f : x=1 ==> res=1].
proof -strict.
 proc.
 skip.
 intros &m h.
 assumption h.
qed.
