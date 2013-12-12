require Logic.
require import Real.

module M = { 
  proc f(x:int) : bool = { 
    return x=1;
  }
}.

lemma foo1 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] = Pr[M.f(x0) @ &m : res].
proof -strict.
 intros &m x0.
 equiv_deno (_:x{1} = x{2} ==> res{1} = res{2}).
 proc.
 wp;skip;intros &m1 &m2 h; rewrite h; split.
 split.
 intros &m1 &m2 H;rewrite H;simplify;split.
qed.

lemma foo2 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] <= Pr[M.f(x0) @ &m : res].
proof -strict.
 intros &m x0.
 equiv_deno (_:x{1} = x{2} ==> res{1} => res{2}).
 proc.
 wp;skip;intros &m1 &m2 h; rewrite h;intros h1;assumption h1.
 split.
 intros &m1 &m2 H;assumption H.
qed.

lemma lequiv : equiv [M.f ~ M.f : x{1} = x{2} ==> res{1} = res{2}].
proof -strict.
  proc;wp;skip;intros &m1 &m2 h; rewrite h; split.
qed.

lemma lfoo1 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] = Pr[M.f(x0) @ &m : res].
proof -strict.
 intros &m x0.
 equiv_deno lequiv.
 split.
 intros &m1 &m2 H;rewrite H;simplify;split.
qed.

lemma lfoo2 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] <= Pr[M.f(x0) @ &m : res].
proof -strict.
 intros &m x0.
 equiv_deno lequiv.
 split.
 intros &m1 &m2 H1 H2; rewrite -H1;apply H2.
qed.

