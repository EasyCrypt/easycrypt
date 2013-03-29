lemma l: forall (x y:int),
  let (u,v) = (x,y) in
  let w = u in
  if true then (lambda z, z = z) w else false
proof.
iota.
intros x y w.
beta.
trivial.
save.
