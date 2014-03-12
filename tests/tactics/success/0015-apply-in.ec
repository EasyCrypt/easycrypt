(* -------------------------------------------------------------------- *)
op a : bool.
op b : bool.
op c : bool.

(* -------------------------------------------------------------------- *)
lemma L1 : (a => b) => a => b.
proof. by intros=> hi h; apply hi in h; apply h. qed.

(* -------------------------------------------------------------------- *)
lemma L2 : (b => a => c) => a => b => c.
proof.
  intros=> hi h1 h2; apply (hi _) in h1.
  by apply h2. by apply h1.
qed.

(* -------------------------------------------------------------------- *)
type t.

op at : t -> bool.
op bt : t -> bool.
op ct : t -> bool.

(* -------------------------------------------------------------------- *)
lemma L3 : (forall x, at x => bt x) => forall x, at x => bt x.
proof. by intros=> hi y h; apply (hi y) in h; apply h. qed.

(* -------------------------------------------------------------------- *)
lemma L4 : (forall x, at x => bt x) => forall x, at x => bt x.
proof. by intros=> hi y h; apply hi in h; apply h. qed.

(* -------------------------------------------------------------------- *)
lemma L5 : (forall x, bt x => at x => ct x) => forall x, at x => bt x => ct x.
proof.
  intros=> hi y h1 h2; apply (hi _ _) in h1.
  by apply h2. by apply h1.
qed.
