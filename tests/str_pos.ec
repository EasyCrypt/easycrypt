


game G = {
  fun f() : int = {
    var x,y,z:int;
    var m : (int,int) map;
    (x,y) = (1,2);
    z = x;
    x = 2;
    m[z]=y; 
    m[m[z]]=m[z]; 
    return m[m[z]]/m[z];
  }
  fun g() : unit = {}
}.



prover z3, eprover, cvc3.
equiv test : G.f ~ G.g : true ==> res{1}=1.
sp 1 1.
wp 3 1.
sp 1 1.
sp 1 1.
wp.
trivial.
save.


