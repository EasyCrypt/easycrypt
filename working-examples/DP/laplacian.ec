(* include "reals.ec". *)




pop lap : (int, int, real) -> real.

axiom lap_spec(v1:int,k:int,eps:real,v2:int) :
  x1=lap(v1,k,eps) ~ x2=lap(v2,k,eps):
  (v1-v2<=k && v2-v1<=k) ==[exp(eps);0%r]==> x1=x2.





  
