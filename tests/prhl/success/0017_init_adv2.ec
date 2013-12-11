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

lemma foo3 : forall (A<:Adv), 
  equiv[G(A).main ~ G(A).main : true ==> ={res} && (glob A){1} = (glob A){2}].
intros A.
proc.
call (_ : ={x} /\ (glob A){1} = (glob A){2} ==>
         ={res} /\ (glob A){1} = (glob A){2}).
(* It could be greate to detect that since 
   O do not have state it is not a problem *)
proc true;[trivial | trivial | ].
proc;skip;trivial.
call (_ : true ==> ={res} /\ (glob A){1} = (glob A){2}).
proc true;try skip;trivial.
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
  Pr[G(A).main() @ &m1 : res = 3] = 
  Pr[G(A).main() @ &m2 : res = 3]. 
intros &m1 &m2.
apply (foo &m1 &m2 A).
save.
