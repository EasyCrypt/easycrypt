require import AllCore.

op foo : int -> int.
op bar : int -> int distr.

module M = {
  proc f() : int = {
    return 0;
  }

  proc g() = {
    var x : int;

    x <- foo (5 + 3);
    x <$ bar (x + 2);

    while (2 * x < 4) {
    }

    x <@ f();
  }
}.


lemma L : hoare[M.g : true ==> true].
proof.
proc.
alias 1 c := (_ + 3).
alias 3 d := (x + _).

fail alias ^ while e := (_ * x).
fail alias ^ <@ e := 3.
abort.
