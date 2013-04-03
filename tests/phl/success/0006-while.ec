require Logic.
module M = { 
  fun f () : int * int = {
    var x, y : int;
    x = 1;
    y = 0;
    while (true) {
      x = 1;
    }
    return (x,y);
  }
}.

lemma foo : hoare [M.f : true ==> res = (1,0)]
proof.
 fun.
 while (x=1).   
 wp;skip;simplify;intros _;split.
 wp;skip;simplify;intros _;split.
save.

module M1 = { 
  fun f () : int * int= {
    var x, y : int;
    x = 1;
    y = 10;
    while (x <> y) {
      x = x;
    }
    return (x,y);
  }
}.

lemma foo1 : hoare [M1.f : true ==> res = (10,10)]
proof.
 fun.
 while (x=1).   
 wp;skip.
 simplify;intros _ h.
(*  elim h. FIXME : bug ? *)
 trivial.
 wp;skip.
 intros _ _;split.
 split .
 intros x h _;rewrite h;split.
save.







