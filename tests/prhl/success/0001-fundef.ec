module M = { 
  proc f (x:int) : int = { return x; }
}.

lemma foo : equiv [M.f ~ M.f : x{1}=x{2} ==> res{1}=res{2}].
proof.
 proc.
 skip.
 intros &m1 &m2 h.
 assumption h.
save.


module type T = {
  proc f() : bool
}.

module M1(A:T) = {
  proc f() : bool = {
    var r : bool;
    r  = A.f();
    return r;
  }
}.

module M2(A:T) = {
  proc f() : bool = {
    var r : bool;
    r  = A.f();
    return r;
  }
}.

lemma test :
  forall (A<:T),
    equiv [M1(A).f ~ M2(A).f : ((glob A){1} = (glob A){2}) ==> res{1} = res{2}].
proof.
  intros A.
  proc.
  call (_ : (glob A){1} = (glob A){2} ==> res{1}=res{2}).
  proc true.
  smt.
  smt.
  skip.
  smt.
save.
