module M = {
  var y : int
  fun f(x:int) : int = {
    y = x;
    y = 1;
    return y;
  }
}.

lemma foo : hoare [M.f : true ==> res = 1 /\ M.y = 1 ]
proof.
 fun.
 app 1 : (M.y = z).
