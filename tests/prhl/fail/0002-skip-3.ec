module M1 = {
  fun f () : unit = { }
}.

module M2 = { 
  fun g () : unit = {
    var x : int;
    x = 2;
  }
}.

lemma foo : equiv [M2.g ~ M2.g : true ==> true].
proof.
  fun.
  skip.