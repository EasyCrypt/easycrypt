require import Int.

module type Or = { 
  proc o (x:int) : int 
}.

module type Adv (O:Or) = { 
  proc * a1 () : unit {}
  proc a2 (x:int) : int {O.o}
}. 

module O = { 
  var w:int
  proc o (x:int) : int = { return x + w; }
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

lemma foo3 : forall (A<:Adv{O}), 
  equiv[G(A).main ~ G(A).main : ={O.w} ==> ={res} && (glob A){1} = (glob A){2}].
intros A.
proc.
call (_ : ={x,O.w} /\ (glob A){1} = (glob A){2} ==>
         ={res} /\ (glob A){1} = (glob A){2}).
proc (={O.w});[trivial | trivial | ].
proc;skip;trivial.
call (_ : ={O.w} ==> ={res} /\ (glob A){1} = (glob A){2}).
proc (={O.w}) ;try skip;trivial.
skip;trivial.
save.

lemma foo : forall &m1 &m2(A<:Adv{O}), 
  O.w{m1} = O.w{m2} =>
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3].
intros &m1 &m2 A Heq.
equiv_deno (foo3 A);trivial.
save.


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
    x = O.o(x); 
    x = L.f();
    return s + x;
  } 
}.

lemma foo1 : forall &m1 &m2,
  O.w{m1} = O.w{m2} =>
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3]. 
intros &m1 &m2.
apply (foo &m1 &m2 A).
save.
