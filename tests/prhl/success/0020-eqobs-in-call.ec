require import Int.

module type Orcl = {
  proc o (x:int) : int 
}.

module type Adv (O:Orcl) = { 
  proc a1 (x:int) : int {* O.o}
  proc a2 (x:int) : int
}.

module O = { 
  var m : int
  var l : int
  proc o (x:int) : int = {
    m = x + m;
    return m;
  }
}.

module G (A:Adv) = {
  module AO = A(O)
  proc main (x:int) : int = { 
    x = AO.a1(x);
    x = O.o(x);
    x = AO.a2(x);
    return x;
  }
}.

equiv foo_0 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l} ==> ={res,O.m,O.l}.
proc.
eqobs_in true true : (={O.m,O.l,x}).
save.

equiv foo_1 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l} ==> ={res,O.m,O.l}.
proc.
eqobs_in.
save.

equiv foo1_0 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l,glob A} ==> ={res,O.m,glob A}.
proc.
eqobs_in true true : (={O.m,glob A,x,O.l}).
save.

equiv foo1_1 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l,glob A} ==> ={res,O.m,glob A}.
proc.
eqobs_in.
save.
