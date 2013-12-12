require import Logic.

lemma l: forall (x y:int),
  let (u,v) = (x,y) in
  let w = u in
  if true then (fun z, z = z) w else false.
proof -strict.
iota.
intros x w.
beta.
split.
qed.
