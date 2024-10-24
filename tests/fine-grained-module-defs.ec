require import AllCore.

module type T  = {
  proc run() : unit
}.

module A (B : T) = {
  var x : int

  proc f(y: int) = {
    x <- x + y;
    B.run();
    return x;
  }
  proc g(y: int) = {
    x <- x - y;
    B.run();
    return x;
  }
}.

module A_count (B : T) = A(B) with {
  var c : int
  proc f [1 - { c <- c + 1;}]
  proc g [1 ~ { c <- c - 1;}, 2 -]
}.

print A_count.

equiv A_A_count (B <: T{-A_count, -A}) : A(B).f ~ A_count(B).f: ={arg, glob B} /\ ={x}(A, A_count) ==> ={res, glob B} /\ ={x}(A, A_count).
proof.
proc.
by call (: true); auto.
qed.
