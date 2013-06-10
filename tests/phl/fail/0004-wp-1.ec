module M = { 
  fun f () : unit = {}
  fun g () : unit = {
    var x : int;
    f();
    x = 1;
  }
}.

lemma foo : hoare [M.g : true ==> true].
proof.
 fun.
 wp 0.