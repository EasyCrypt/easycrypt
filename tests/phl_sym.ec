require import AllCore Int.


module M = {
  proc f1(a: int) = {
    var c : int;
    c <- a;
    return c;
  }

  proc f2(a: int) = {
    var d;
    d <@ f1 (a);
    
    return d;
  }
}.

lemma aux (a_: int) : hoare[M.f1 : a_ = a ==> res = a_].
proof. proc; auto. qed.

lemma test : equiv[M.f2 ~ M.f2 : ={arg} ==> ={res}].
proc.
inline {1}.
symmetry.
proc change {2} [1-2] : { a0 <- a; }. 
abort.
