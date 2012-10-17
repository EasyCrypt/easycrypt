pred P : (int, int).

axiom PSnnS : forall (x : int, y : int), P (x+1, y) => P (x, y+1).
axiom P_0_2 : P(1+1, 0).

lemma G' : P(0, 2).

lemma L  : forall (x : int, y : int), P (x+2, y) => P (x+1, y+1).
lemma L' : forall (x : int, y : int), P (x+2, y) => P (x  , y+2).
