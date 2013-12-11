require import Int.

module type Or = { 
  proc o (x:int) : int 
}.

module type Adv (O:Or) = { 
  proc * a1 () : unit {}
  proc a2 (x:int) : int {O.o}
}. 

module O = { 
  proc o (x:int) : int = { return x; }
}.

module G (A:Adv) = { 

  module A1 = A(O)

  proc main () : int = {
    var x : int;
    A1.a1();
    x = A1.a2(3);
    return x;
  }
}.

axiom foo : forall &m1 &m2(A<:Adv), 
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3].

module L = { 
  var x : int
  proc f () : int = { return x; }
}.

module A (O:Or) = {
  var s : int
  proc a1 () : unit = { 
    s = 1; 
    L.x = 2; 
  }
  proc a2(x:int) : int = { 
    var z : int;
    x = O.o(x); 
    x = L.f();
    return s + x + z;
  } 
}.

lemma foo1 : forall &m1 &m2,
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3]. 
intros &m1 &m2.
apply (foo &m1 &m2 A).
save.