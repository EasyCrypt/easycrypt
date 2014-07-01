lemma L (a c : bool) (b : int -> bool) (x : int):
  (c => a) => (forall x, b x => c) => (b x => a).
proof. by move=> h1 h2 /h2 /h1 ->. qed.
