module M = { 
  proc f () : unit = {
    var x, y : int;
    x = 1;
    y = 0;
    x = 2;
  }
}.

equiv foo : M.f ~ M.f : true ==> true.
proof.
 proc.
 swap {1} 1 2 4.