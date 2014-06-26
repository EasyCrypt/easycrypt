(* -------------------------------------------------------------------- *)
lemma L (x y z t : int): x = y => y = z => t = z => x = t.
proof. by move=> h ->> <<-; rewrite h; reflexivity. qed.
