(* include "reals.ec". *)



cnst k : int.
cnst eps : real.


op lap_op (l,a:int) = exp(-((|l%r-a%r|)/(k%r/eps))).

axiom lap_lem : forall (a1:int,a2:int,l:int),
   |a1-a2| <= k =>
   lap_op(l,a1) <= exp(eps)*lap_op(l,a2).


(* abs (a1 - a2) <= k => *)
(*  exp(-(|l%r - a1%r| / (k%r / eps))) <= *)
(*   exp(eps) * exp(-(|l%r - a2%r| / (k%r / eps))) + 0%r *)
(* . *)

timeout 10.


pop lap (a:real) = (z:int) -> exp(-((|z%r-a|) / (k%r/eps) ) ).

pop lap2 : real -> int.


game G = {
  var x : int
  fun f() :unit = {
    x = lap2 (0%r);
    x = lap (0%r);
  }

}
.

lemma lap_spec(a1:int,a2:int) :
  x1=lap(a1%r) ~ x2=lap(0%r)+a2:
  (|a1-a2|)<=k ==[exp(eps);0%r]==> x1=x2.


lemma lap_spec2(a1:int,a2:int) :
  x1=lap(a1%r) ~ x2=lap(a2%r):
  (|a1-a2|)<=k ==[exp(eps);0%r]==> x1=x2.



game gameF = {
  var x : int
  fun f () : int = {
    return x;
  }

}
.

game gameF' = {
  var x : int
  var y : int
  fun f () : int = {
    return x;
  }

}
.

axiom eps_pos : 0%r < eps.
axiom asd : 1%r <= exp(eps).


equiv asd : gameF.f ~ gameF'.f : ={x} ==[exp(eps);0%r]==> ={res}.
trivial.
save.




  
