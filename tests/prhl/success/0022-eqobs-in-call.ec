require import Int.

module type Orcl = {
  proc o1 (x:int) : int 
  proc o2 (x:int) : int
}.

module type Adv (O:Orcl) = { 
  proc * a1 (x:int) : int { O.o1}
  proc a2 (x:int) : int
}.

module O1 = { 
  var m : int
  var l : int
  var w : int

  proc o1 (x:int) : int = {
    m = x + m;
    return m;
  }
  proc o2 (x:int) : int = {
    l = l + x + m + w;
    return m;
  }
}.

module O2 = { 
  var m : int
  var l : int

  proc o1 (x:int) : int = {
    m = x + m;
    return m;
  }
  proc o2 (x:int) : int = {
    l = l + x + m + 2;
    return m;
  }
}.


module G1 (A:Adv) = {
  module AO = A(O1)
  proc main (x:int) : int = { 
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
  proc main (x:int) : int = { 
    x = AO.a1(x); 
    x = O2.o1(x);
    x = O2.o2(x);
    x = AO.a2(x); 
    return x;
  }
}.

equiv foo_0 (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
  ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
    ={res} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
proof -strict.
 proc.
 sim (: O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) / (O1.w{1} = 2)
          : (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} /\ ={x}).
  proc;wp;skip;trivial.
 wp;skip;trivial.
qed.

equiv foo_1 (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
  ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
    ={res} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
proof -strict.
 proc.
 sim (:O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) / (O1.w{1} = 2) .
   proc;wp;skip;trivial.
 wp;skip;trivial.
qed.

equiv foo1_0 (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
      ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
      ={res,glob A} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
proc.
  sim (: O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) / (O1.w{1} = 2) :
     (O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} /\ ={x,glob A}). 
   proc;wp;skip;trivial.
 wp;skip;trivial.
qed.

equiv foo1_1 (A<:Adv {O1,O2} ) : G1(A).main ~ G2(A).main : 
      ={x} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2} ==> 
      ={res,glob A} /\ O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}.
proc.
  sim (:O1.m{1} = O2.m{2} /\ O1.l{1} = O2.l{2}) / (O1.w{1} = 2) .
   proc;wp;skip;trivial.
 wp;skip;trivial.
qed.

