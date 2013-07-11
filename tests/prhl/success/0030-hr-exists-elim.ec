
require import Int.
require import Bool.

module X = {
  fun f(x : int) : int = {
    return x - 1;
  }


  fun main(y : int) : bool = {
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
proof.
intros y.
fun; skip; smt.
qed.

lemma X_main :
  equiv[X.main ~ X.main :
        ={y} ==>
        ={res} /\ res{1}].
proof.
 fun.
 exists * y{1}.
 elim *.
 intros yy.
 call (X_f yy).
 trivial.
save.

