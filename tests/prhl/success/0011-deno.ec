require Logic.
require import Real.

module M = { 
  fun f(x:int) : bool = { 
    return x=1;
  }
}.

lemma foo1 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] = Pr[M.f(x0) @ &m : res]
proof.
 intros m x0.
 equiv_deno (x{1} = x{2}) (res{1} = res{2}).
 fun.
 wp;skip;intros m1 m2 h; rewrite h; split.
 split.
 intros m1 m2 H;rewrite H;simplify;split.
save.

lemma foo2 : forall &m (x0:int), 
  Pr[M.f(x0) @ &m : res ] <= Pr[M.f(x0) @ &m : res]
proof.
 intros m x0.
 equiv_deno (x{1} = x{2}) (res{1} => res{2}).
 fun.
 wp;skip;intros m1 m2 h; rewrite h;intros h1;assumption h1.
 split.
 intros m1 m2 H; assumption H.
save.
