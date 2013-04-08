module M = { 
  fun f () : unit = {
    var x : int;
    var y : int; 
    x = 0;
    x = 1;
    y = 2;
    y = 3;
  }
}.

equiv foo : M.f ~ M.f : true ==> true
proof.
  fun.   
  swap {1} 2 3 3.
  swap {1} 3 4 4.
  swap {1} 1 2 3.
  swap {1} 1 3 4.
  swap {2} 2 3 3.
  swap {2} 3 4 4.
  swap {2} 1 2 3.
  swap {2} 1 3 4.
  swap 1 3 4.
  swap [1..2] 2.
  swap [3..4] -2.
  swap 2 2.
  swap -1.
  swap 1.
  swap {1} [2..3] 1.
  swap {2} [2..3] -1.
  wp;skip;intros m1 m2 h;assumption h.
save.

