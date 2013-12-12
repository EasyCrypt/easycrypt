(* -------------------------------------------------------------------- *)
type nat = [ O | S of nat].

op add (x y : nat) =
  with x = O   => y
  with x = S x => S (add x y).

lemma add0n y: add O y = y.
proof -strict. by smt. qed.

lemma addSn x y: add (S x) y = S (add x y).
proof -strict. by smt. qed.

lemma addn0 x: add x O = x.
proof -strict.
  elimT x => {x}; first by rewrite add0n.
  by intros=> n IH; rewrite addSn IH.
qed.

lemma addnS x y: add x (S y) = S (add x y).
proof -strict.
  elimT x => {x}; first by rewrite !add0n.
  by intros=> n IH; rewrite !addSn IH.
qed.

lemma addnC x y: add x y = add y x.
proof -strict.
  elimT x => {x}; first by rewrite add0n addn0.
  by intros=> n IH; rewrite addSn addnS IH.
qed.

lemma addnA x y z: add (add x y) z = add x (add y z).
proof -strict.
  elimT x => {x}; first by rewrite !add0n.
  by intros=> n IH; rewrite !addSn IH.
qed.  

(* -------------------------------------------------------------------- *)
type 'a list = [
  | Nil
  | Cons of 'a & 'a list].

op size ['a] (xs : 'a list) =
  with xs = Nil       => O
  with xs = Cons y ys => S (size ys).

lemma size_nil ['a]: size Nil<:'a> = O by [].
lemma size_cons ['a] x xs: size (Cons<:'a> x xs) = S (size xs) by [].

op cat ['a] (xs1 xs2 : 'a list) : 'a list =
  with xs1 = Nil       => xs2
  with xs1 = Cons y ys => Cons y (cat ys xs2).

lemma cat_nil ['a] xs: cat Nil<:'a> xs = xs by [].
lemma cat_cons ['a] x xs xs': cat (Cons<:'a> x xs) xs' = Cons x (cat xs xs') by [].

lemma size_cat ['a] (xs1 xs2 : 'a list):
  size (cat xs1 xs2) = add (size xs1) (size xs2).
proof -strict.
  elimT xs1 => {xs1}.
  by rewrite cat_nil size_nil add0n.
  by intros=> y ys IH; rewrite cat_cons size_cons IH size_cons addSn.
qed.

op nseq ['a] (n : nat) (x : 'a) =
  with n = O   => Nil
  with n = S p => Cons x (nseq p x).

lemma nseqO ['a] (x : 'a): nseq O x = Nil by [].
lemma nseqS ['a] n (x : 'a): nseq (S n) x = Cons x (nseq n x) by [].

lemma size_nseq ['a] n (x : 'a) : size (nseq n x) = n.
proof -strict.
  elimT n => {n}; first by rewrite nseqO size_nil.
  by intros=> n IH; rewrite nseqS size_cons IH.
qed.

op nth ['a] (x : 'a) (n : nat) (xs : 'a list) =
  with n = O  , xs = Nil       => x
  with n = O  , xs = Cons y ys => y
  with n = S p, xs = Nil       => x
  with n = S p, xs = Cons y ys => nth x p ys.

lemma nth_O_Nil  (x : 'a)       : nth x O Nil = x by [].
lemma nth_O_Cons (x : 'a) y ys  : nth x O (Cons y ys) = y by [].
lemma nth_S_Nil  (x : 'a) n     : nth x (S n) Nil = x by [].
lemma nth_S_Cons (x : 'a) n y ys: nth x (S n) (Cons y ys) = nth x n ys by [].

lemma nth_nil (x : 'a) n: nth x n Nil = x.
proof -strict.
  elimT n => {n}; first by rewrite nth_O_Nil.
  by intros=> n _; rewrite nth_S_Nil.
qed.

op subn n p =
  with n = O   , p = O    => O
  with n = O   , p = S p' => O 
  with n = S n', p = O    => n
  with n = S n', p = S p' => subn n' p'.

lemma subOO: subn O O = O by [].
lemma subSO: forall n, subn (S n) O = S n by [].
lemma subOS: forall n, subn O (S n) = O by [].
lemma subSS: forall n p, subn (S n) (S p) = subn n p by [].

lemma subn0 n: subn n O = n.
proof -strict.
  elimT n => {n}; first by rewrite subOO.
  by intros=> n _; rewrite subSO.
qed.

op le (n p : nat) = (subn n p) = O.
op lt (n p : nat) = le (S n) p.

lemma nth_default (x : 'a) n l: le (size l) n => nth x n l = x.
proof -strict.
  rewrite /le; generalize n; elimT l => {l}.
    by intros=> n; rewrite nth_nil.
  intros=> y ys IH n; elimT n => {n}.
    by rewrite size_cons subn0; smt.
  intros=> n _ h; rewrite nth_S_Cons; apply IH.
  by generalize h; rewrite size_cons subSS.
qed.
