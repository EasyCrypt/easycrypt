require import Int.

module type Orcl = {
  fun o1 (x:int) : int 
  fun o2 (x:int) : int
}.

module type Adv (O:Orcl) = { 
  fun a1 (x:int) : int {* O.o1}
  fun a2 (x:int) : int
}.

module O = { 
  var m : int
  var l : int
  fun o1 (x:int) : int = {
    m = x + m;
    return m;
  }
  fun o2 (x:int) : int = {
    l = l + x + m;
    return m;
  }
}.

module G (A:Adv) = {
  module AO = A(O)
  fun main (x:int) : int = { 
    x = AO.a1(x);
    x = O.o1(x);
    x = O.o2(x);
    x = AO.a2(x);
    return x;
  }
}.

equiv foo (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l} ==> ={res,O.m,O.l}.
fun.
eqobs_in true (={O.m,O.l,x}) true.
fun (={O.m}).    
 trivial.
 trivial.
fun.
 eqobs_in true (={O.m}) true.
fun.
 eqobs_in (={O.m}) true true.
fun.
 eqobs_in (={O.l,O.m}) true true.
fun (={O.l,O.m}).
trivial.
trivial.
fun.
eqobs_in (={O.l,O.m}) true true.
fun.
eqobs_in (={O.l,O.m}) true true.
save.

equiv foo1 (A<:Adv {O} ) : G(A).main ~ G(A).main : ={x,O.m,O.l,glob A} ==> ={res,O.m,glob A}.
fun.
eqobs_in true (={O.m,glob A,x,O.l}) true.
fun (={O.m}).    
 trivial.
 trivial.
fun.
 eqobs_in (={O.m}) true true.
fun.
 eqobs_in (={O.m}) true true.
fun. eqobs_in true (={O.l,O.m}) true.
fun (={O.l,O.m}).
trivial.
trivial.
conseq * (_ : ={x,O.m} ==> ={res,O.m} );trivial.
fun. eqobs_in (={O.m}) true true.
fun. eqobs_in (={O.m, O.l}) true true.
save.

