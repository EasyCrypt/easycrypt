(* -------------------------------------------------------------------- *)
datatype nat = O | S of nat.

op add (x y : nat) =
  with x = O   => y
  with x = S x => S (add x y).

lemma add0n y: add O y = y.
proof. by smt. qed.

lemma addSn x y: add (S x) y = S (add x y).
proof. by smt. qed.

lemma addn0 x: add x O = x.
proof.
  elim/nat_ind x => {x}; first by rewrite add0n.
  by intros=> n IH; rewrite addSn IH.
qed.

lemma addnS x y: add x (S y) = S (add x y).
proof.
  elim/nat_ind x => {x}; first by rewrite !add0n.
  by intros=> n IH; rewrite !addSn IH.
qed.

lemma addnC x y: add x y = add y x.
proof.
  elim/nat_ind x => {x}; first by rewrite add0n addn0.
  by intros=> n IH; rewrite addSn addnS IH.
qed.

lemma addnA x y z: add (add x y) z = add x (add y z).
proof.
  elim/nat_ind x => {x}; first by rewrite !add0n.
  by intros=> n IH; rewrite !addSn IH.
qed.  

(* -------------------------------------------------------------------- *)
datatype list =
  | Nil
  | Cons of nat & list.

op size (xs : list) =
  with xs = Nil       => O
  with xs = Cons y ys => S (size ys).

lemma size_nil: size Nil = O by [].
lemma size_cons x xs: size (Cons x xs) = S (size xs) by [].

op cat (xs1 xs2 : list) =
  with xs1 = Nil       => xs2
  with xs1 = Cons y ys => Cons y (cat ys xs2).

lemma cat_nil xs: cat Nil xs = xs by [].
lemma cat_cons x xs xs': cat (Cons x xs) xs' = Cons x (cat xs xs') by [].

lemma size_cat xs1 xs2: size (cat xs1 xs2) = add (size xs1) (size xs2).
proof.
  elim/list_ind xs1 => {xs1}.
  (**) by rewrite cat_nil size_nil add0n.
  (**) by intros=> y ys IH; rewrite cat_cons size_cons IH size_cons addSn.
qed.
