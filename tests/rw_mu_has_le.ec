require import AllCore List Distr DInterval StdBigop.
import Bigreal.

module M = { 
  proc f () : int = { 
    var x : int;
    x <$ [0..10];
    return x;
  }
}.

op l : int list.

lemma foo &m : 
  Pr [ M.f() @ &m : has (fun x => res = x) l] <= 
  BRA.big predT (fun x => Pr [ M.f() @ &m : res = x]) l.
proof.
  by rewrite Pr [mu_has_le].
qed.
  
