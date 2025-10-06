module type BT = {
  proc p(): unit
}.

module Foo(Bar: BT) = {
  var b: bool

  proc p() = {
    b <- true;
  }

  proc q() = {
    b <- true;
    Bar.p();
  }
}.

lemma L (Bar<: BT) &m: Pr[Foo(Bar).p() @&m: !Foo.b] = Pr[Foo(Bar).q() @&m: !Foo.b].
proof.
fail byupto.
abort.
