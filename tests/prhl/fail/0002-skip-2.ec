module M1 = {
  fun f () : unit = { }
}.

module M2 = { 
  fun g () : unit = {
    var x : int;
    x = 2;
  }
}.

lemma foo : equiv [M2.f ~ M1.g : true ==> true].
proof.
  fun.
  skip.