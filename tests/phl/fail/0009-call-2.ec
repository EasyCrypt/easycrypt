require Logic.
module M = {
  var y : int
  var z : int
  fun f (x:int) : int = { 
    y = x;
    return 3;
  }

  fun g (w:int) : int = {
    var r : int;
    r := f(w);
    return r;
  }
}.

lemma foo : 
  forall (xi zi:int),
  hoare [M.g : M.z=zi /\ w = xi ==> res = 3 /\ M.z = zi /\ M.y = xi]
proof.
  intros xi zi;fun.
  call (x=xi) (res = 3 /\ M.y = w).

