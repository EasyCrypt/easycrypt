module M1 = {
  proc f () : unit = { }
}.

module M2 = { 
  proc g () : unit = {
    var x : int;
    x = 2;
  }
}.

lemma foo : equiv [M1.f ~ M2.g : true ==> true].
proof.
  proc.
  skip.