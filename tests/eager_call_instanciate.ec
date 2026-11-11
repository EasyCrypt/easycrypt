require import AllCore.

section SC.
module S = {
  proc f(x:int) = { }

  proc g (x:int) = { return x;}
 
}.

lemma eager_f_sample y : eager [
  S.f(y);, S.g ~ S.g, S.f(y); :
    ={x} ==> ={res} ].
proof.
eager proc; inline *; swap{1} 1; sim.
qed.

lemma eager_f_sample' z : eager [
  S.f(z);, S.g ~ S.g, S.f(z); :
    ={x} ==> ={res} ].
proof.
apply (eager_f_sample z).
qed.

end section SC.

op b : bool.

lemma toto : b.
have /= h := eager_f_sample.
have := h 1.
admitted.

