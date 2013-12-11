require Logic.

module M = { 
  proc f () : int * int = {
    var x : int;
    var y : int;
    x = 1;
    y = 0;
    while (true) {
      x = 1;
    }
    return (x,y);
  }
}.

lemma foo : hoare [M.f : true ==> res = (1,0)].
proof.
 proc.
 while (x=1).   
 wp;skip;simplify;split.
 wp;skip;simplify;split.
save.

module M1 = { 
  proc f () : int * int= {
    var x : int;
    var y : int;
    x = 1;
    y = 10;
    while (x <> y) {
      x = x;
    }
    return (x,y);
  }
}.

lemma foo1 : hoare [M1.f : true ==> res = (10,10)].
proof.
 proc.
 while (x=1).   
   wp;skip.
   intros _ h.
   elim h;intros h1 _; assumption h1.
 wp;skip => /= x -> //.
save.
