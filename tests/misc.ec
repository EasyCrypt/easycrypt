include "def.ec".

type my_abs_type.
type my_def_type = bool * int.

cnst kk : t1.
cnst k : int.
cnst k3 : int = 3.
cnst kv : int = k.
cnst b1, b2, b3 : bool.
cnst c1, c2, c3 : int = 0.

op my_op1 : int -> int as my_op1.
op my_op2 : (int, int) -> int as my_op2.
op my_op3 : () -> int as my_op3.

adversary f (a:int, b:int) : int {(int, int)->bool}.

game G1 = {

  var x, y : int

  
  fun f1 (a:int, b:int) : bool = {
    var r : bool = {0,1};
    var r2 : bitstring{k} = {0,1}^k;
    var r3, r4 : int;
    var l : my_def_type;
    r3 = x^k;
    l = (true, 3);
    if (r) 
      { x = a; y = b; }
    else
      x = b;
    return r;
    }

  abs f = f {f1}


  fun f2 (z:int) : int = {
    var a, b : int = 3;
    var c : int ;
    var cond : bool;
    b = 1 + my_op2 (a, 2);
    c = f (a, b);
    cond = f1 (a+b, [0..10]);
    z = cond ? 3 : 4;
    return (z + x + k);
    }

  fun f4 (z:int) : int = {
   return z+1;
   }	

  fun f5 (z:int) : int = {
    var b : int = x+z;
    return b+1;
  }	
}.

game G2 = {
  var x : int
  var y : int

  fun g (a:int) : int = { return a+1; }

  fun f (a:int) : unit = {
    var l : int list = 3::[];
    var lb : bool list = [];
    (* return 0; *)
    }

  fun f4 (z:int) : int = {
   return z+1;
  }

  fun f5 (z:int) : int = {
    var a : int = x+z;
    return a+1;
  }

}.

game G3 = {
   (* test empty game *)
}.

prover "alt-ergo".

equiv name : G1.f4 ~ G2.f4 : ={z} ==> ={res}
  && forall (x1:int), (x1{1} + 1) = (1 + x1{2})
  && forall (x2:int), x2{1} + 1 = 1 + x2{2}
by auto.

equiv name1 : G1.f4 ~ G2.f4 : ={z} ==> ={res} &&
  forall (x1:int), x1 + 1 = 1 + x1 &&
  forall (x2:int), x2 + 1 = 1 + x2 by auto.

equiv name5 : G1.f4 ~ G2.f4 : ={z} ==> ={res} &&
  forall (x1:int), x1{1} + 1 = 1 + x1{2} &&
  forall (x2:int), x2{1} + 1 = 1 + x2{2} by auto.
