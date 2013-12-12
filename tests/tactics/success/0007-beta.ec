lemma l: forall (x:int), (fun y, y = y) x.
proof -strict.
beta.
smt.
qed.