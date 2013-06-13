module M = { 
  fun f () : unit = { 
    var x : int;
    x = 1;
  }
}.

lemma foo : hoare [ M.f : true ==> true].
proof.
 fun.
 skip.