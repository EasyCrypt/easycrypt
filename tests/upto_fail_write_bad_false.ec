module Foo = {
  var b: bool

  proc p() = {
    b <- true;
  }

  proc q() = {
    b <- true;
    b <- false;
  }
}.

lemma L &m: Pr[Foo.p() @&m: !Foo.b] = Pr[Foo.q() @&m: !Foo.b].
proof.
fail byupto.
abort.
