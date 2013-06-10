require Logic.
require import Int.

module M1 = { 
  fun f () : int * int= {
    var x : int;
    var y : int;
    x = 1;
    y = 10;
    while (x <> y) {
      x = x + 1;
    }
    return (x,y);
  }
}.

lemma test1 : hoare [M1.f : true ==> true].
proof.
  fun.
  splitwhile (x<=5) : 3.
  while (x<=y).
  wp; skip; trivial.
  while (x<=y).
  wp; skip; trivial.
  wp; skip; trivial.
save.

lemma test2 : equiv [M1.f ~ M1.f : true ==> true].
proof.
  fun.
  splitwhile (x<=5) : {2} 3.
  splitwhile (x<=5) : {2} 3.
  admit.
save.
