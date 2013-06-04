require Logic.
require import Int.

module M = { 
  var y : int
  fun f(x:int) : int * int = {
    var i : int = 0;
    while (i <= 10) { x = x + i; i = i+1; }
    return (x,y);
  }
}.

equiv foo : M.f ~ M.f : 
  M.y{1} = M.y{2} /\ x{1}=x{2} ==> res{1} = res{2} /\ M.y{1} = M.y{2}
proof.
 fun.
 while (x{1} = x{2} /\ i{1} = i{2}).
   wp;skip.
   simplify.
   intros &m1 &m2 h.
   elim h;clear h;intros h1 _.
   elim h1;intros heq1 heq2;clear h1.
   rewrite heq1;rewrite heq2. simplify. split.

 wp; skip.
 intros &m1 &m2 h;elim h;intros heq1 heq2;rewrite heq1; rewrite heq2; simplify.
 clear h heq1 heq2.
 intros x1 i1 x2 i2 _ _ h1;elim h1;intros heq1 heq2;subst; simplify.
 split.
save.

module type T = { fun f() : unit }.

module MM(A:T) = { 
  var y : int
  fun f(x:int) : int * int = {
    var i : int = 0;
    while (i <= 10) { x = x + i; i = i+1;A.f();}
    return (x,y);
  }
}.

equiv foo (A<:T) : MM(A).f ~ MM(A).f : 
  (glob A){1} = (glob A){2} /\ M.y{1} = M.y{2} /\ x{1}=x{2} ==> res{1} = res{2} /\ M.y{1} = M.y{2}
proof.
 fun.
 while (x{1} = x{2} /\ i{1} = i{2}).
   call ((glob A){1} = (glob A){2}) (true).
   wp;skip.
   simplify.
   intros &m1 &m2 h.
   elim h;clear h;intros h1 _.
   elim h1;intros heq1 heq2;clear h1.
   rewrite heq1;rewrite heq2. simplify. split.

 wp; skip.
 intros &m1 &m2 h;elim h;intros heq1 heq2;rewrite heq1; rewrite heq2; simplify.
 clear h heq1 heq2.
 intros x1 i1 x2 i2 _ _ h1;elim h1;intros heq1 heq2;subst; simplify.
 split.
save.