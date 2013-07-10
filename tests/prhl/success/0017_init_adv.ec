require import Int.

module type Or = { 
  fun o (x:int) : int 
}.

module type Adv (O:Or) = { 
  fun a1 () : unit {*}
  fun a2 (x:int) : int {O.o}
}. 

module O = { 
  var w:int
  fun o (x:int) : int = { return x + w; }
}.

module G (A:Adv) = { 

  module A1 = A(O)

  fun main () : int = {
    var x : int;
    A1.a1();
    x = A1.a2(3);
    return x;
  }
}.

lemma foo3 : forall (A<:Adv{O}), 
  equiv[G(A).main ~ G(A).main : ={O.w} ==> ={res} && (glob A){1} = (glob A){2}].
intros A.
fun.
call (_ : ={x,O.w} /\ (glob A){1} = (glob A){2} ==>
         ={res} /\ (glob A){1} = (glob A){2}).
fun (={O.w});[trivial | trivial | ].
fun;skip;trivial.
call (_ : ={O.w} ==> ={res} /\ (glob A){1} = (glob A){2}).
fun (={O.w}) ;try skip;trivial.
skip;trivial.
save.

lemma foo : forall &m1 &m2(A<:Adv), 
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3].
intros &m1 &m2 A.
equiv_deno (foo3 A);trivial.
save.


module L = { 
  var x : int
  fun f () : int = { return x; }
}.

module A (O:Or) = {
  var s : int
  fun a1 () : unit = { 
    s = 1; 
    L.x = 2;
  }
  fun a2(x:int) : int = { 
    x = O.o(x); 
    x = L.f();
    return s + x;
  } 
}.

lemma foo1 : forall &m1 &m2,
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3]. 
intros &m1 &m2.
apply (foo &m1 &m2 A).
save.
