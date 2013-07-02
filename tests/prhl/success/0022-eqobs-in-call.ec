require import Int.

module type Orcl = {
  fun o1 (x:int) : int 
  fun o2 (x:int) : int
}.

module type Adv (O:Orcl) = { 
  fun a1 (x:int) : int {* O.o1}
  fun a2 (x:int) : int
}.

module O1 = { 
  var m : int
  var l : int
  var w : int

  fun o1 (x:int) : int = {
    m = x + m;
    return m;
  }
  fun o2 (x:int) : int = {
    l = l + x + m + w;
    return m;
  }
}.

module O2 = { 
  var m : int
  var l : int

  fun o1 (x:int) : int = {
    m = x + m;
    return m;
  }
  fun o2 (x:int) : int = {
    l = l + x + m + 2;
    return m;
  }
}.


module G1 (A:Adv) = {
  module AO = A(O1)
  fun main (x:int) : int = { 
    O1.w = 2;
    x = AO.a1(x); 
    x = O1.o1(x); 
    x = O1.o2(x);
    x = AO.a2(x); 
    return x;
  }
}.

module G2 (A:Adv) = {
  module AO = A(O2)
  fun main (x:int) : int = { 
    x = AO.a1(x); 
    x = O2.o1(x);
    x = O2.o2(x);
    x = AO.a2(x); 
    return x;
  }
}.

equiv foo (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
  ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
    ={res} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
proof.
 fun.
 eqobs_in (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) (O1.w{1} = 2)
          (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} /\ ={x}).
   fun;wp;skip;trivial.
 wp;skip;trivial.
save.

equiv foo1 (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
      ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
      ={res,glob A} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
fun.
  eqobs_in (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) (O1.w{1} = 2)
     (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} /\ ={x,glob A}). 
   fun;wp;skip;trivial.
 wp;skip;trivial.
save.

