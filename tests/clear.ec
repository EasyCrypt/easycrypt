lemma L: true.
pose x:=false.
clear x.
(* `x` is now unbound *)
pose x:=false.
pose y:=x.
pose z:=y.
clear -y. 
(* `z` is unbound, but `x` is not, since `y` depends on it *)
pose z:=x.
clear y.
pose y:=z.
clear. 
(* everything is unbound, since nothing is in the goal *)
pose x:=true.
pose y:=false.
clear. 
(* we cannot clear `x` since it is in the goal,
   but `y` is not used so it becomes unbound *)
pose y:= x.
abort.
