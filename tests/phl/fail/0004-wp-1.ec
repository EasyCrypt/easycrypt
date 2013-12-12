module M = { 
  proc f () : unit = {}
  proc g () : unit = {
    var x : int;
    f();
    x = 1;
  }
}.

lemma foo : hoare [M.g : true ==> true].
proof -strict.
 proc.
 wp 0.