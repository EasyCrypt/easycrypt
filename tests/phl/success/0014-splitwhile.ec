require Logic.
require import Int.

module M1 = { 
  proc f () : int * int= {
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
proof -strict.
  proc.
  splitwhile 3 : (x<=5).
  while (x<=y).
  wp; skip; smt.
  while (x<=y).
  wp; skip; smt.
  wp; skip; smt.
qed.

lemma test2 : equiv [M1.f ~ M1.f : true ==> true].
proof -strict.
  proc.
  splitwhile {2} 3 : (x<=5).
  splitwhile {2} 3 : (x<=5).
  admit.
qed.
