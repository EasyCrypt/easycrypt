require import Int.
module M = { 
  var x,w: int
  var y : bool
  fun f (z:int) : int * bool = { 
    x = z + w;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test : M.f ~ M.f : ={z,M.w,M.y} ==> ={M.x,M.y,res}.
fun.
eqobs_in (={M.x,M.y,z}).
save.

module M0 = { 
  var y : bool
  var x,w: int
  fun f (z:int) : int * bool = { 
    var z0, w0: int;
    w0 = w;
    z0 = z;
    x = z + w;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test0 : M.f ~ M0.f : M.w{1} = M0.w{2} /\ M.y{1} = M0.y{2} /\ ={z}  ==> 
                M.x{1} = M0.x{2} /\ M.y{1} = M0.y{2} /\ ={res}.
fun.
eqobs_in (M.x{1} = M0.x{2} /\ M.y{1} = M0.y{2} /\ ={z}).
save.

module M1 = { 
  var y : bool
  var x,w: int
  fun f (z:int) : int * bool = { 
    var z0, w0: int;
    w0 = w;
    z0 = z;
    x = z0 + w0;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test1 : M.f ~ M1.f : M.w{1} = M1.w{2} /\ M.y{1} = M1.y{2} /\ ={z}  ==> 
                M.x{1} = M1.x{2} /\ M.y{1} = M1.y{2} /\ ={res}.
fun.
eqobs_in (M.x{1} = M1.x{2} /\ M.y{1} = M1.y{2} /\ ={z}).
save.

  
