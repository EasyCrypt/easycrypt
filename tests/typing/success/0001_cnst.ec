op c1 : unit = tt.
op c2 : bool = true.
op c3 : bool = false.
op c4 : int  = 10.
(* op c5 : int  = -10. need to require int*)
  
type t.
op c : t.
op k1 : int = 0.
op k2 : _ = (0,true).
op k3 : (int * bool) * t = (k2,c).
op k4 : int * bool * t = (10,false,c).

