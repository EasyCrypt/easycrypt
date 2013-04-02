module M = { 
  fun f (x:int) : int = { return x; }
}.

lemma foo : hoare [M.f : x=1 ==> res=1]
proof.
 fun.
 skip.
 intros m h.
 assumption h.
save.