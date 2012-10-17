pop random : int -> bool.
pop lap : (int, int, real) -> real.

game toto = {
  fun main (x:int) : bool = {
     var b1,b2:bool;
     b1 = random(x);
     b2 = random(x);
     return (b1 = b2);
  }
}.

equiv test : toto.main ~ toto.main : ={x} ==> ={res}.
trivial.
save.

axiom foo (v1:int,k:int,eps:real,v2:int) : 
   x1 = {0,1}^k ~ x2 = lap(v1,k,eps) : true  ==> true.

axiom foo2(v1:int,k:int,eps:real,v2:int) : 
  x1 = lap(v1,k,eps) ~ x2 = lap(v2,k,eps) :
  (v1-v2<=k && v2-v1<=k) ==[exp(eps);0%r]==> x1 = x2.


cnst k, k1, k2 : int.
axiom k_spec : k = k1 + k2.

op [||] : (bitstring{k1},bitstring{k2}) -> bitstring{k1+k2} as append.
op [==] : (bitstring{k1+k2}, bitstring{k}) -> bool as eq_bitstr.

axiom rnd_bs_append() : 
x1 = {0,1}^k1 || {0,1}^k2
  ~
x2 = {0,1}^k : k=3 ==[1%r;0%r]==> x1 == x2 && k=3.

game G = {
  fun toto() : bitstring{k1+k2} = {
    var x : bitstring{k1+k2};
    x = {0,1}^k1 || {0,1}^k2;
    return x;
  }

  fun titi() : bitstring{k} = {
    var x : bitstring{k};
    x = {0,1}^k;
    return x;
  }

}.


equiv test' : G.toto ~ G.titi : k=3 ==> res{1}==res{2}.
apply : rnd_bs_append().
trivial.
save.


