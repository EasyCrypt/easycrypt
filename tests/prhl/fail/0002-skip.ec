module M1 = {
  fun f () : unit = { }
}.

module M2 = { 
  fun g () : unit = {
    var x : int;
    x = 2;
  }
}.

lemma foo : equiv [M1.f ~ M2.g : true ==> true]
proof.
  fun.
  skip.