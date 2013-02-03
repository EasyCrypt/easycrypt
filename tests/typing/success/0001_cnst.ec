cnst c1 : unit = tt.
cnst c2 : bool = true.
cnst c3 : bool = false.
cnst c4 : int  = 10.
(* cnst c5 : int  = -10. need to require int*)
  
type t.
cnst c : t.
cnst k1 : int = 0.
cnst k2 : _ = (0,true).
cnst k3 : (int * bool) * t = (k2,c).
cnst k4 : int * bool * t = (10,false,c).

