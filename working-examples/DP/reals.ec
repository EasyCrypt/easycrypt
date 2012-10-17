(* auxiliary real lemmas *)
axiom pow_zero : forall (x:real), (x)^(0%r) = 1%r.





(* exp axioms *)
timeout 20.
axiom real_exp_mon : forall (x:real,y:real), x<y => exp(x)<exp(y).
axiom pos_exp : forall (x:real), 0%r < exp(x).
axiom real_auxlemma9' : forall (x,y:real), exp(x)=1%r/exp(-x).
axiom pow_exp : forall (x:real,y:real), exp(x)^y = exp(x*y). (*  *)
lemma real_auxlemma9'' : forall (x,y:real), y*exp(-x)=y/exp(x). (*  *)

lemma asd' : forall (x,y:real), exp(x+y)/exp(y) = exp(x).
