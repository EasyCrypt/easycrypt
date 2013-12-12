require Logic.

module M = {
  var y : int
  var z : int
  proc f (x:int) : int = { 
    y = x;
    return 3;
  }
}.

lemma foo : 
  hoare [M.f : true ==> true].
proof -strict.
 proc.
 call ( _ : true ==> true). 