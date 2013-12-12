lemma L1 : forall (f : bool), f = f.
proof -strict. by intros=> f; congr. qed.

lemma L2 : forall (f : 'a -> bool), f = f.
proof -strict. by intros=> f; congr. qed.

lemma L3 : forall (f : 'a -> 'b -> bool), f = f.
proof -strict. by intros=> f; congr. qed.

lemma L4 : forall (f : 'a -> bool) x1 x2,
  x1 = x2 => f x1 = f x2.
proof -strict. by intros=> f x1 x2 eq_x; congr. qed.

lemma L5 : forall (f : 'a -> 'b -> bool) x1 x2,
  x1 = x2 => f x1 = f x2.
proof -strict. by intros=> f x1 x2 eq_x; congr. qed.

lemma L6 : forall (f : 'a -> 'b -> 'c -> bool) x1 x2 y1 y2,
  x1 = x2 => y1 = y2 => f x1 y1 = f x2 y2.
proof -strict. by intros=> f x1 x2 y1 y2 eq_x eq_y; congr. qed.

lemma L7 : forall (f : 'a -> 'b -> 'c -> bool) x1 x2 y1 y2 z1 z2,
  x1 = x2 => y1 = y2 => z1 = z2 => f x1 y1 z1 = f x2 y2 z2.
proof -strict. by intros=> f x1 x2 y1 y2 z1 z2 eq_x eq_y eq_z; congr. qed.
