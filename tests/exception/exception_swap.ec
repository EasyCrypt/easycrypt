require import AllCore.

exception exn1.

module M = {
  var w : int
  var x : int
  var y : int
  var z : int

  proc f() : unit = {
  w <- 42;
  x <- 42;
  raise exn1;
  y <- 42;
  z <- 42;
  }
}.

lemma f_correct :
  hoare[M.f : true ==> false | exn1 => M.x = 42 /\ M.w = 42].
proof. proc. wp. skip. smt(). qed.

lemma f_wrong :
  hoare[M.f : M.x = 0 ==> false | exn1 => M.x = 0].
proof. proc.
  swap 1 1.
  swap 4 1.
  fail swap 1 2.
  fail swap 1 3.
  fail swap 3 1.
abort.
