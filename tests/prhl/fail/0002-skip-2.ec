module M1 = {
  proc f () : unit = { }
}.

module M2 = { 
  proc g () : unit = {
    var x : int;
    x = 2;
  }
}.

lemma foo : equiv [M2.f ~ M1.g : true ==> true].
proof.
  proc.
  skip.