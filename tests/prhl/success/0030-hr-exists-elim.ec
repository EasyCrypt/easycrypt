
require import Int.
require import Bool.

module X = {
  proc f(x : int) : int = {
    return x - 1;
  }


  proc main(y : int) : bool = {
    var x : int;
    var b : bool;
    x = f(y);
    return x < y;
  }
}.

lemma X_f :
  forall (y : int),
  equiv[X.f ~ X.f :
        x{1} <= y /\ ={x} ==>
        res{1} < y /\ ={res}].
proof -strict.
intros y.
proc; skip; smt.
qed.

lemma X_main :
  equiv[X.main ~ X.main :
        ={y} ==>
        ={res} /\ res{1}].
proof -strict.
 proc.
 exists * y{1}.
 elim *.
 intros yy.
 call (X_f yy).
 trivial.
qed.

