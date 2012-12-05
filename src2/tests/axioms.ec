op eq : (int,int) -> bool.
op plus : (int, int) -> int.
axiom toto : forall (x:int), eq ( plus(x,x), 0). 


theory TEST.
  axiom toto : false.
(*  axiom toto : false. *)
end TEST.

theory TEST2.
  axiom toto : true.
end TEST2.  

theory ARITH.
op eq1 : (int,int) -> bool.
op plus1 : (int, int) -> int.
axiom toto : forall (x:int), eq1 ( plus1(x,x), 0). 
end ARITH.

theory TEST3.
  axiom toto : forall (x:int), ARITH:>eq1 ( ARITH:>plus1(x,x), 0). 
end TEST3.  

