require import Int.

module type Orcl = {
  fun o (x:int) : int 
}.

module type Adv (O:Orcl) = { 
  fun a1 (x:int) : int {* O.o}
  fun a2 (x:int) : int
}.

module O = { 
  var m : int
  var l : int
  fun o (x:int) : int = {
    m = x + m;
    return m;
  }
}.

module G (A:Adv) = {
  module AO = A(O)
  fun main (x:int) : int = { 
    x = AO.a1(x);
    x = O.o(x);
    x = AO.a2(x);
    return x;
  }
}.

equiv foo (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l} ==> ={res,O.m,O.l}.
fun.
eqobs_in true true (={O.m,O.l,x}).
save.

equiv foo1 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l,glob A} ==> ={res,O.m,glob A}.
fun.
eqobs_in true true (={O.m,glob A,x,O.l}).
save.
