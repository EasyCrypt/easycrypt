module M = { 
  proc f () : unit = { 
    var x : int;
    x = 1;
  }
}.

lemma foo : hoare [ M.f : true ==> true].
proof -strict.
 proc.
 skip.