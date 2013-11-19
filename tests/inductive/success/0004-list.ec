(* -------------------------------------------------------------------- *)
require import Int.

(* -------------------------------------------------------------------- *)
datatype 'a list =
  | Nil
  | Cons of 'a & 'a list.

op cat (l1 l2 : 'a list) : 'a list =
  with l1 = Nil => l2
  with l1 = Cons y ys => Cons y (cat ys l2).

lemma cat0s xs: cat<:'a> Nil xs = xs by [].
lemma cat_cons x xs ys: cat<:'a> (Cons x xs) ys = Cons x (cat xs ys) by [].

lemma cats0 xs: cat<:'a> xs Nil = xs.
proof.
  elim/list_ind xs => {xs}; first by rewrite cat0s.
  by intros=> y ys IH; rewrite cat_cons IH.
qed.

lemma catA (xs ys zs : 'a list): cat xs (cat ys zs) = cat (cat xs ys) zs.
proof.
  elim/list_ind xs => {xs}; first by rewrite !cat0s.
  by intros=> x xs IH; rewrite !cat_cons IH.
qed.

op size (xs : 'a list) : int =
  with xs = Nil       => 0
  with xs = Cons y ys => 1 + (size ys).

lemma size_nil: size Nil<:'a> = 0 by [].
lemma size_cons y ys: size (Cons<:'a> y ys) = 1 + size ys by [].

lemma ge0_size (xs : 'a list): 0 <= size xs.
proof. by elim/list_ind xs => {xs}; smt. qed.

op nth x n (xs : 'a list) : 'a =
  with xs = Nil       => x
  with xs = Cons y ys => if n = 0 then y else (nth x (n-1) ys).

lemma nth_nil x n: nth x n Nil<:'a> = x.
proof. by smt. qed.

lemma nth_cons x n y ys:
  nth x n (Cons<:'a> y ys) = if n = 0 then y else (nth x (n-1) ys).
proof. by smt. qed.

lemma ltz_neqAle n m: (n < m) <=> (n <> m) && (n <= m).
proof. by smt. qed.

lemma nth_lt0 (x : 'a) n xs: n < 0 => nth x n xs = x.
proof.
  generalize n; elim/list_ind xs => {xs}.
    by intros=> n; rewrite nth_nil.
  intros=> y ys IH n; rewrite nth_cons ltz_neqAle => [nz_n le0_n].
  by case (n = 0); [smt|intros=> _; apply IH; smt].
qed.

lemma nth_default (x : 'a) n xs: size xs <= n => nth x n xs = x.
proof.
  generalize n; elim/list_ind xs => {xs}.
    by intros=> n _; rewrite nth_nil.
  intros=> y ys IH n; rewrite size_cons nth_cons => h.
  by case (n = 0); [by smt | intros=> nz_n; apply IH; smt].
qed.

lemma size_cat (s1 s2 : 'a list): size (cat s1 s2) = size s1 + size s2.
proof.
  elim/list_ind s1 => {s1}; first by rewrite cat0s size_nil.
  by intros=> x s1 IH; rewrite cat_cons !size_cons IH; smt.
qed.
