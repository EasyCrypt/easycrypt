require import AllCore.

module M = {
  proc f(x : int) : int = {
    return x + 1;
  }

  proc g(x : int, y : int) : int = {
    x <@ f(x);
    x <- x + 1;
    return 2*x;
  }
}.

lemma fP : hoare[M.f : 0 <= x ==> 1 <= res].
proof. by proc; auto=> /#. qed.

pred p : int.

lemma gP (y_ : int) :
  hoare[M.g : 0 < x /\ y = y_ /\ p y ==> 0 < res /\ p y_].
proof.
proc=> /=.
ecall ->> (fP); first by move=> &hr |> /#.
by auto=> &hr |> /#.
qed.
