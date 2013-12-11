require import Int.
module M = { 
  var x,w: int
  var y : bool
  proc f (z:int) : int * bool = { 
    x = z + w;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test_0 : M.f ~ M.f : ={z,M.w,M.y} ==> ={M.x,M.y,res}.
proc.
sim true true : (={M.x,M.y,z}).
save.

equiv test_1 : M.f ~ M.f : ={z,M.w,M.y} ==> ={M.x,M.y,res}.
proc.
sim true : (={M.x,M.y,z}).
save.

equiv test_2 : M.f ~ M.f : ={z,M.w,M.y} ==> ={M.x,M.y,res}.
proc.
sim : (={M.x,M.y,z}).
save.

equiv test_3 : M.f ~ M.f : ={z,M.w,M.y} ==> ={M.x,M.y,res}.
proc.
sim.
save.



module M0 = { 
  var y : bool
  var x,w: int
  proc f (z:int) : int * bool = { 
    var z0, w0: int;
    w0 = w;
    z0 = z;
    x = z + w;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test0_0 : M.f ~ M0.f : M.w{1} = M0.w{2} /\ M.y{1} = M0.y{2} /\ ={z}  ==> 
                M.x{1} = M0.x{2} /\ M.y{1} = M0.y{2} /\ ={res}.
proc.
sim true true : (M.x{1} = M0.x{2} /\ M.y{1} = M0.y{2} /\ ={z}).
save.

equiv test0_1 : M.f ~ M0.f : M.w{1} = M0.w{2} /\ M.y{1} = M0.y{2} /\ ={z}  ==> 
                M.x{1} = M0.x{2} /\ M.y{1} = M0.y{2} /\ ={res}.
proc.
sim.
save.

module M1 = { 
  var y : bool
  var x,w: int
  proc f (z:int) : int * bool = { 
    var z0, w0: int;
    w0 = w;
    z0 = z;
    x = z0 + w0;
    y = y && y;
    return (z + x, y);
  }
}.

equiv test1_0 : M.f ~ M1.f : M.w{1} = M1.w{2} /\ M.y{1} = M1.y{2} /\ ={z}  ==> 
                M.x{1} = M1.x{2} /\ M.y{1} = M1.y{2} /\ ={res}.
proc.
sim true true : (M.x{1} = M1.x{2} /\ M.y{1} = M1.y{2} /\ ={z}).
save.

equiv test1_1 : M.f ~ M1.f : M.w{1} = M1.w{2} /\ M.y{1} = M1.y{2} /\ ={z}  ==> 
                M.x{1} = M1.x{2} /\ M.y{1} = M1.y{2} /\ ={res}.
proc.
sim.
save.

  
