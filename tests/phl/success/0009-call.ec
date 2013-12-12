require Logic.
module M = {
  var y : int
  var z : int
  proc f (x:int) : int = { 
    y = x;
    return 3;
  }

  proc g (x:int) : int = {
    var r : int;
    r  = f(x);
    return r;
  }
}.

lemma foo : 
  forall (xi zi:int),
  hoare [M.g : M.z=zi /\ x = xi ==> res = 3 /\ M.z = zi /\ M.y = xi].
proof -strict.
  intros xi zi;proc.
  call ( _ : x = xi ==> res = 3 /\ M.y = xi).
    proc;wp;skip.
    intros &m _;subst;simplify;split.
  skip.
  intros &m h;elim h;clear h;intros _ _;subst;simplify;split.
qed.
