(*-------------------------------------------------------------------- *)
require import AllCore List IntDiv.

axiom iteri_red (n : int) (opr : int -> int -> int) (x : int) :
  0 < n => iteri n opr x = opr (n-1) (iteri (n-1) opr x).

hint simplify iteri_red.

(* BIG enough so that unfolding unfolding will be untrackable *)    
axiom ge0_test: 0 < 2^100000000000000000000000000.

hint [rigid] exact : ge0_test.

lemma foo (l : int list) (x : int) : [x] = x :: l.
proof. fail by done. abort.
