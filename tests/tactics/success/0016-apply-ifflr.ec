(* -------------------------------------------------------------------- *)
op a : bool.
op b : bool.
op c : bool.

(* -------------------------------------------------------------------- *)
lemma L1 : (a <=> b) => a => b.
proof. by intros=> h ha; apply h; assumption. qed.

(* -------------------------------------------------------------------- *)
lemma L2 : (c => (a <=> b)) => c => a => b.
proof.
  by intros=> h hc ha; apply h; [apply hc|apply ha].
qed.

(* -------------------------------------------------------------------- *)
lemma L3 : (a <=> (c => b)) => c => a => b.
proof.
  by intros=> h hc ha; apply h; [apply ha|apply hc].
qed.

(* -------------------------------------------------------------------- *)
type t.

op at : t -> bool.
op bt : t -> bool.
op ct : t -> bool.

lemma L4 : (forall x, at x <=> bt x) => forall y, at y => bt y.
proof. by intros=> h y ha; apply h; assumption. qed.

(* -------------------------------------------------------------------- *)
lemma L5 : (forall x, ct x => (at x <=> bt x)) => forall y, ct y => at y => bt y.
proof.
  by intros=> h y hc ha; apply h; [apply hc|apply ha].
qed.

(* -------------------------------------------------------------------- *)
lemma L6 : (forall x, at x <=> (ct x => bt x)) => forall y, ct y => at y => bt y.
proof.
  by intros=> h y hc ha; apply h; [apply ha|apply hc].
qed.
