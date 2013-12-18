require Logic.
module M1 = {
  var y : int
  var z : int
  proc f (x:int) : int = { 
    y = x;
    return 3;
  }

  proc g (x:int) : int = {
    var r : int;
    r  = f(x);
    return r;
  }
}.

module M2 = {
  var y : int
  var z : int
  proc f (w:int) : int = { 
    y = w;
    return 3;
  }

  proc g (w:int) : int = {
    var r : int;
    r  = f(w);
    return r;
  }
}.


lemma foo : 
  equiv [M1.g ~ M2.g : M1.z{1}=M2.z{2} /\ M1.y{1} = M2.y{2} /\ x{1} = w{2} 
        ==> res{1} = res{2} /\ M1.z{1} = M2.z{2} /\ M1.y{1} = M2.y{2}].
proof -strict.
  proc.
  call (_ : x{1}=w{2} ==> res{1} = res{2} /\ M1.y{1} = M2.y{2}).
    proc;wp;skip.
    intros &m1 &m2 h;simplify;assumption.
  skip.
  intros &m1 &m2 h;elim h;intros h1 h2.
  elim h2;intros h2 h3.
  rewrite h1; rewrite h3;simplify;split.
qed.

module type Adv = {
  proc f() : unit
}.

module M(A:Adv) = {

  proc g() : unit = {
    A.f();
  }

}.

lemma foo1 : forall (A<:Adv {M}), hoare [M(A).g : true ==> true].
proof -strict.
intros A.
proc.
call (_ : true ==> true).
proc true;progress.
skip;progress.
qed.
