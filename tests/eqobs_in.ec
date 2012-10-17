game G = {
  var x : int
  fun f (u,v:int) : int = {
    var y,z : int;
    y = u + v;
    z = x + y;
    return z;
  }
}.

equiv test : G.f ~ G.f : ={x,u,v} ==> ={x,res}
 by auto (={x}).
(*
eqobs_in (={x}) (true) (={x,z}).
trivial.
save.
*)

game G1 = {
  var x : int
  fun f (u,v:int) : int = {
    var y,z : int;
    y = u + v;
    if (u = v) {
      z = x + y;
    } else {
      x = 3;
      z = x + u;
    }
    return z;
  }
}.

equiv test1 : G1.f ~ G1.f : ={x,u,v} ==> ={x,res} by auto (={x}).
(*
eqobs_in (={x}) (true) (={x,z}).
trivial.
save.
*)
game G2 = {
  var x : int
  fun G (i:int) : int = {
    x = x + 1;
    return (i+x);
  }
  fun f (u,v:int) : int = {
    var y,z : int;
    y = u + v;
    z = G(x + y);
    z = z + u;
    return z;
  }
}.

equiv test2 : G2.f ~ G2.f : ={x,u,v} ==> ={x,res}
by auto (={x}).
(*
eqobs_in (={x}) (true) (={x,z}).
trivial.
save.
*)
game G3 = {
  var x : int
  fun G (i:int) : int = {
    x = x + 1;
    return (i+x);
  }

  fun f (u,v:int) : int = {
    var y,z : int;
    y = u + v;
    if (u = v) {
      z = G(x + y);
    } else {
      x = 3;
      z = x + u;
    }
    z = z + u;
    return z;
  }
}.

equiv test3 : G3.f ~ G3.f : ={x,u,v} ==> ={x,res}
by auto (={x}).
(*
eqobs_in (={x}) (true) (={x,z}).
trivial.
save.
*)

