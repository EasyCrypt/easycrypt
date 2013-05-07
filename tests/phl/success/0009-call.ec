require Logic.
module M = {
  var y : int
  var z : int
  fun f (x:int) : int = { 
    y = x;
    return 3;
  }

  fun g (x:int) : int = {
    var r : int;
    r := f(x);
    return r;
  }
}.

lemma foo : 
  forall (xi zi:int),
  hoare [M.g : M.z=zi /\ x = xi ==> res = 3 /\ M.z = zi /\ M.y = xi]
proof.
  intros xi zi;fun.
  call (x=xi) (res = 3 /\ M.y = xi).
    fun;wp;skip.
    intros &m _;subst;simplify;split.
  skip.
  intros &m h;elim h;clear h;intros _ _;subst;simplify.
  intros y h;assumption h.
save.
