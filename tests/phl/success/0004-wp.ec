require Logic.
module M = {
  proc f (w x:int) : int = {
    var y : int;
    var z : int;
    y = 1;
    z = x;
    x = y;
    y = z; 
    return x;
  }
}.

lemma foo : hoare [M.f : true ==> res = 1 ].
proof.
 proc.
 wp.
 skip;intros _ _;split.
qed.

lemma foo1 : hoare [M.f : true ==> res = 1 ].
proof.
 proc.
 wp 1.
 wp 0.
 skip;intros _ _;split.
qed.

    
