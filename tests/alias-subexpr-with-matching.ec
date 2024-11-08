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
alias c := (_ + 3) @ 1.
alias d := (x + _) @ 3.

fail alias e := (_ * x) @ ^ while.
fail alias e := 3 @ ^ <@.
abort.
