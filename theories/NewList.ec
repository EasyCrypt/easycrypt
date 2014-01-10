(* -------------------------------------------------------------------- *)
require import Int.

(* -------------------------------------------------------------------- *)
op pred1  ['a] (c : 'a) = fun (x : 'a), c = x.
op predT  ['a] = fun (x : 'a), true.
op pred0  ['a] = fun (x : 'a), false.
op predC  ['a] (P : 'a -> bool) = fun (x : 'a), ! (P x).
op predC1 ['a] (c : 'a) = fun (x : 'a), c <> x.

pred preim ['a 'b] (f : 'a -> 'b) p x = p (f x).

op int_of_bool (b : bool) = if b then 1 else 0.

(* -------------------------------------------------------------------- *)
theory IntTh.
  lemma nosmt subzz (z : int): z - z = 0 by [].

  lemma nosmt lezz (z : int): z <= z by [].
  lemma nosmt ltzz (z : int): z < z <=> false by [].

  lemma nosmt ltzNge (x y : int): (x <  y) <=> !(y <= x) by [].
  lemma nosmt lezNgt (x y : int): (x <= y) <=> !(y <  x) by [].

  lemma nosmt gez_le (x y : int): (x >= y) <=> (y <= x) by [].
  lemma nosmt gtz_lt (x y : int): (x >  y) <=> (y <  x) by [].
end IntTh.

import IntTh.

(* -------------------------------------------------------------------- *)
type 'a list = [
  | "[]"
  | (::) of  'a & 'a list
].

op size (xs : 'a list) =
  with xs = "[]"      => 0
  with xs = (::) y ys => 1 + (size ys).

lemma size_ge0 (s : 'a list): 0 <= size s.
proof. by elim s=> //= x s; smt. qed.

op (++) (s1 s2 : 'a list) =
  with s1 = "[]"      => s2
  with s1 = (::) x s1 => x :: (s1 ++ s2).

op rcons (s : 'a list) (z : 'a) =
  with s = "[]"      => [z]
  with s = (::) x s' => x :: (rcons s' z).

op last_ (x : 'a) s =
  with s = "[]"      => x
  with s = (::) y ys => last_ y ys.

lemma cat0s (s : 'a list): [] ++ s = s.
proof. by []. qed.

lemma cats0 (s : 'a list): s ++ [] = s.
proof. by elim s=> //= x s ->. qed.

lemma cat1s (x : 'a) (s : 'a list): [x] ++ s = x::s.
proof. by []. qed.

lemma cats1 (s : 'a list) (z : 'a): s ++ [z] = rcons s z.
proof. by elim s => //= x s ->. qed.

lemma cat_cons (x : 'a) s1 s2: (x :: s1) ++ s2 = x :: (s1 ++ s2).
proof. by []. qed.

lemma catA (s1 s2 s3 : 'a list): s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
proof. by elim s1=> //= x s1 ->. qed.

lemma size_cat (s1 s2 : 'a list): size (s1 ++ s2) = size s1 + size s2.
proof. by elim s1=> // x s1 /= ->; smt. qed.

lemma last_cons (x y : 'a) (s : 'a list): last_ x (y :: s) = last_ y s.
proof. by []. qed.

lemma size_rcons s (x : 'a):
  size (rcons s x) = (size s) + 1.
proof. by rewrite -cats1 size_cat /=. qed.

lemma cat_rcons (x : 'a) s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
proof. by rewrite -cats1 -catA. qed.

lemma rcons_cat (x : 'a) s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
proof. by rewrite -!cats1 catA. qed.

op nth x (xs : 'a list) n : 'a =
  with xs = "[]"      => x
  with xs = (::) y ys => if n = 0 then y else (nth x ys (n-1)).

lemma nth_default (z : 'a) s n: size s <= n => nth z s n = z.
proof.
  elim s n => //= x s IHs n; case (n = 0).
    by intros=> ->; smt.
    by intros=> _ _; rewrite IHs; smt.
qed.

lemma nth_neg (x0 : 'a) s n: n < 0 => nth x0 s n = x0.
proof. elim s n => //=; smt. qed.

lemma nth_cat (x0 : 'a) s1 s2 n:
  nth x0 (s1 ++ s2) n = if n < size s1 then nth x0 s1 n else nth x0 s2 (n - size s1).
proof.
  case (n < 0) => [n_lt0|n_ge0]; first by smt.
  by elim s1 n n_ge0; smt.
qed.

op mem (s : 'a list) (z : 'a) =
  with s = "[]"      => false
  with s = (::) x s' => (z = x) \/ mem s' z.

lemma in_nil (x : 'a): mem [] x = false.
proof. by []. qed.

lemma in_cons y s (x : 'a): mem (y :: s) x <=> (x = y) \/ (mem s x).
proof. by []. qed.

lemma mem_head (x : 'a) s: mem (x :: s) x.
proof. by []. qed.

lemma mem_seq1 (x y : 'a): mem [y] x <=> (x = y).
proof. by []. qed.

lemma mem_seq2 (x y1 y2 : 'a):
  mem [y1; y2] x <=> (x = y1 \/ x = y2).
proof. by []. qed.

lemma mem_seq3 (x y1 y2 y3 : 'a):
  mem [y1; y2; y3] x <=> (x = y1 \/ x = y2 \/ x = y3).
proof. by []. qed.

lemma mem_seq4 (x y1 y2 y3 y4 : 'a):
  mem [y1; y2; y3; y4] x <=> (x = y1 \/ x = y2 \/ x = y3 \/ x = y4).
proof. by []. qed.

op uniq (s : 'a list) =
  with s = "[]"      => true
  with s = (::) x s' => !(mem s' x) /\ uniq s'.

op undup (s : 'a list) =
  with s = "[]"      => []
  with s = (::) x s' => if mem s' x then undup s' else x :: undup s'.

lemma size_undup (s : 'a list): size (undup s) <= size s.
proof. by elim s => //= x s IHs; smt. qed.

lemma mem_undup (s : 'a list): forall x, mem (undup s) x = mem s x.
proof. intros=> x; elim s => //= y s IHs; smt. qed.

lemma undup_uniq (s : 'a list): uniq (undup s).
proof. by elim s => //= x s IHs; case (mem s x); smt. qed.

lemma undup_id (s : 'a list): uniq s => undup s = s.
proof. by elim s => //= x s IHs; smt. qed.

op filter (p : 'a -> bool) xs =
  with xs = "[]"      => []
  with xs = (::) y ys => if p y then y :: filter p ys else filter p ys.

lemma filter_pred0 (s : 'a list): filter pred0 s = [].
proof. by elim s. qed.

lemma filter_predT (s : 'a list): filter predT s = s.
proof. by elim s => //= x s ->. qed.

op count ['a] (p : 'a -> bool) xs =
  with xs = "[]"      => 0
  with xs = (::) y ys => (int_of_bool (p y)) + (count p ys).

lemma count_ge0 (p : 'a -> bool) s: 0 <= count p s.
proof. by elim s=> //= x s; smt. qed.

lemma count_size p (s : 'a list): count p s <= size s.
proof. by elim s => //= x s; smt. qed.

op has (p : 'a -> bool) xs =
  with xs = "[]"      => false
  with xs = (::) y ys => (p y) \/ (has p ys).

op all (p : 'a -> bool) xs =
  with xs = "[]"      => true
  with xs = (::) y ys => (p y) /\ (all p ys).

lemma hasP p (s : 'a list): has p s <=> (exists x, mem s x /\ p x).
proof.
  elim s => //= y s IHs; case (p y) => py.
    by rewrite orTb /=; exists y; smt.
  by rewrite orFb IHs; split; elim=> x []; smt.
qed.

lemma allP p (s : 'a list):
  all p s <=> (forall x, mem s x => p x).
proof.
  elim s=> //= x s [IH1 IH2]; split.
    by elim=> _ h y []; [intros=> -> // | apply IH1].
  intros=> h; split; [by apply h | apply IH2].
  by intros=> y y_in_s; apply h; right.
qed.

lemma count_filter p (s : 'a list): count p s = size (filter p s).
proof. by elim s => //= x s ->; case (p x). qed.

lemma count_pred0 (s : 'a list): count pred0 s = 0.
proof. by rewrite count_filter filter_pred0. qed.

lemma count_predT (s : 'a list): count predT s = size s.
proof. by rewrite count_filter filter_predT. qed.

lemma has_count p (s : 'a list): has p s <=> (0 < count p s).
proof. by elim s => //= x s -> /=; case (p x); smt. qed.

lemma has_pred0 (s : 'a list): has pred0 s <=> false.
proof. by rewrite has_count count_pred0. qed.

lemma has_predT (s : 'a list): has predT s <=> (0 < size s).
proof. by rewrite has_count count_predT. qed.

lemma all_count p (s : 'a list): all p s <=> (count p s = size s).
proof. by elim s => //= x s; case (p x) => _ /=; smt. qed.

lemma all_pred0 (s : 'a list): all pred0 s <=> (size s = 0).
proof. by rewrite all_count count_pred0 eq_sym. qed.

lemma all_predT (s : 'a list): all predT s.
proof. by rewrite all_count count_predT. qed.

lemma eq_filter p1 p2 (s : 'a list): p1 = p2 => filter p1 s = filter p2 s.
proof. by intros=> h; elim s=> //= x l; rewrite h => ->. qed.

lemma eq_count p1 p2 (s : 'a list): p1 = p2 => count p1 s = count p2 s.
proof. by intros=> h; rewrite !count_filter (eq_filter _ p2). qed.

lemma eq_has p1 p2 (s : 'a list): p1 = p2 => has p1 s <=> has p2 s.
proof. by intros=> h; rewrite !has_count (eq_count _ p2). qed.

lemma eq_all p1 p2 (s : 'a list): p1 = p2 => has p1 s <=> has p2 s.
proof. by intros=> h; rewrite !has_count (eq_count _ p2). qed.

lemma has_sym (s1 s2 : 'a list): has (mem s1) s2 <=> has (mem s2) s1.
proof. smt. qed.

lemma has_pred1 (z : 'a) s: has (pred1 z) s <=> mem s z.
proof. smt. qed.

lemma filter_all p (s : 'a list): all p (filter p s).
proof. by elim s => //= x s IHs; case (p x). qed.

lemma all_filterP p (s : 'a list): all p s <=> filter p s = s.
proof.
  split; last by intros=> <-; apply filter_all.
  by elim s => //= x s IHs [-> Hs]; rewrite IHs.
qed.

lemma filter_id p (s : 'a list): filter p (filter p s) = filter p s.
proof. by apply all_filterP; apply filter_all. qed.

lemma filter_cat p (s1 s2 : 'a list): filter p (s1 ++ s2) = filter p s1 ++ filter p s2.
proof. by elim s1 => //= x s1 ->; case (p x). qed.

lemma count_cat p (s1 s2 : 'a list): count p (s1 ++ s2) = count p s1 + count p s2.
proof. by rewrite !count_filter filter_cat size_cat. qed.

lemma has_cat p (s1 s2 : 'a list): has p (s1 ++ s2) <=> has p s1 \/ has p s2.
proof. by elim s1 => //= x s1 IHs; rewrite IHs; smt. qed.

lemma all_cat p (s1 s2 : 'a list): all p (s1 ++ s2) <=> all p s1 /\ all p s2.
proof. by elim s1 => //= x s1 IHs; rewrite IHs. qed.

lemma mem_filter (p : 'a -> bool) x s:
  mem (filter p s) x <=> p x /\ (mem s x).
proof. by elim s => //= y s IHs; smt. qed.

lemma filter_uniq (s : 'a list) p: uniq s => uniq (filter p s).
proof. elim s => //= x s IHs [Hx Hs]; smt. qed.

op perm_eq ['a] (s1 s2 : 'a list) =
  all (fun x, count (pred1 x) s1 = count (pred1 x) s2) (s1 ++ s2).

lemma perm_eqP (s1 s2 : 'a list):
  perm_eq s1 s2 <=> (forall p, count p s1 = count p s2).
proof. admit. qed.

lemma perm_eq_refl (s : 'a list): perm_eq s s.
proof. by apply perm_eqP. qed.

lemma perm_eq_sym (s1 s2 : 'a list): perm_eq s1 s2 <=> perm_eq s2 s1.
proof. by rewrite !perm_eqP; smt. qed.

lemma perm_eq_trans (s2 s1 s3 : 'a list):
  perm_eq s1 s2 => perm_eq s2 s3 => perm_eq s1 s3.
proof. by rewrite !perm_eqP => h1 h2 p; rewrite h1 h2. qed.

lemma perm_eqlP (s1 s2 : 'a list):
  perm_eq s1 s2 <=> (forall s, perm_eq s1 s <=> perm_eq s2 s).
proof.
  split; last by intros=> ->; rewrite perm_eq_refl.
  intros=> h s; split; last by apply perm_eq_trans.
  by apply perm_eq_trans; apply perm_eq_sym.
qed.

lemma perm_catC (s1 s2 : 'a list): perm_eq (s1 ++ s2) (s2 ++ s1).
proof. by rewrite !perm_eqP => p; rewrite !count_cat; smt. qed.

lemma perm_catCl (s1 s2 : 'a list):
  forall s, perm_eq (s1 ++ s2) s <=> perm_eq (s2 ++ s1) s.
proof. by rewrite -perm_eqlP perm_catC. qed.

lemma perm_cat2l (s1 s2 s3 : 'a list):
  perm_eq (s1 ++ s2) (s1 ++ s3) <=> perm_eq s2 s3.
proof.
  by rewrite !perm_eqP; split=> h p; cut := h p; rewrite !count_cat; smt.
qed.

lemma perm_cat2r (s1 s2 s3 : 'a list):
  perm_eq (s2 ++ s1) (s3 ++ s1) <=> perm_eq s2 s3.
proof. by do 2! rewrite perm_eq_sym perm_catCl; apply perm_cat2l. qed.

lemma perm_catCAl (s1 s2 s3 : 'a list):
  forall s, perm_eq (s1 ++ s2 ++ s3) s <=> perm_eq (s2 ++ s1 ++ s3) s.
proof. by rewrite -!perm_eqlP perm_cat2r perm_catC. qed.

lemma perm_cons (x : 'a) s1 s2:
  perm_eq (x :: s1) (x :: s2) <=> perm_eq s1 s2.
proof. by generalize (perm_cat2l [x]) => /= h; apply h. qed.

lemma perm_eq_mem (s1 s2 : 'a list):
  perm_eq s1 s2 => forall x, mem s1 x <=> mem s2 x.
proof. by rewrite perm_eqP => h x; rewrite -!has_pred1 !has_count h. qed.

lemma perm_eq_size (s1 s2 : 'a list):
  perm_eq s1 s2 => size s1 = size s2.
proof. by rewrite perm_eqP=> h; rewrite -!count_predT h. qed.

op rem (z : 'a) s =
  with s = "[]"      => []
  with s = (::) x s' => if x = z then s' else x :: (rem z s').

lemma rem_id (z : 'a) s: ! mem s z => rem z s = s.
proof.
  elim s => //= y s IHs; rewrite -nor; elim.
  intros=> neq_yz s_notin_z; rewrite IHs // (eq_sym y).
  by cut ->: (z = y) <=> false.
qed.

lemma perm_to_rem (z : 'a) s : mem s z => perm_eq s (z :: rem z s).
proof.
  elim s => //= y s IHs; rewrite eq_sym perm_eq_sym.
  rewrite -ora_or; elim; first by intros=> -> /=; rewrite perm_eq_refl.
  rewrite -neqF => -> /= z_in_s; rewrite -(cat1s z) -(cat1s y) catA.
  by rewrite perm_catCAl /= perm_cons perm_eq_sym IHs.
qed.

lemma size_rem (x : 'a) s: mem s x => size (rem x s) = (size s) - 1.
proof.
  intros=> h; apply perm_to_rem in h; apply perm_eq_size in h.
  by rewrite h; smt.
qed.

op drop n (xs : 'a list) =
  with xs = "[]"      => []
  with xs = (::) y ys =>
    if n <= 0 then xs else drop (n-1) ys.

lemma drop0 (s : 'a list): drop 0 s = s.
proof. by elim s. qed.

lemma drop_neg n (s : 'a list): n < 0 => drop n s = s.
proof. by elim s => //= x s IHs n_lt0; smt. qed.

lemma drop_oversize n (s : 'a list):
  size s <= n => drop n s = [].
proof. by elim s n; smt. qed.

lemma drop_size (s : 'a list): drop (size s) s = [].
proof. by rewrite drop_oversize. qed.

lemma drop_cons n x (s : 'a list):
  drop n (x :: s) = if 0 < n then drop (n-1) s else x :: s.
proof. by rewrite /= lezNgt; case (0 < n). qed.

lemma size_drop n (s : 'a list):
  0 <= n => size (drop n s) = max 0 (size s - n).
proof. by elim s n => //=; smt. qed.

lemma drop_cat n (s1 s2 : 'a list):
    drop n (s1 ++ s2) =
      if n < size s1 then drop n s1 ++ s2 else drop (n - size s1) s2.
proof. by elim s1 n => //=; smt. qed.

lemma drop_size_cat n (s1 s2 : 'a list):
  size s1 = n => drop n (s1 ++ s2) = s2.
proof. by intros=> <-; rewrite drop_cat subzz ltzz drop0. qed.

op take n (xs : 'a list) =
  with xs = "[]"      => []
  with xs = (::) y ys =>
    if n <= 0 then [] else y :: take (n-1) ys.

lemma take0 (s : 'a list): take 0 s = [].
proof. by elim s. qed.

lemma take_neg n (s : 'a list): n < 0 => take n s = [].
proof. by elim s; smt. qed.

lemma take_oversize n (s : 'a list):
  size s <= n => take n s = s.
proof. by elim s n; smt. qed.

lemma take_size (s : 'a list): take (size s) s = s.
proof. by rewrite take_oversize. qed.

lemma take_cons n x (s : 'a list):
  take n (x :: s) = if 0 < n then x :: take (n-1) s else [].
proof. by rewrite /= lezNgt; case (0 < n). qed.

lemma size_take n (s : 'a list):
  0 <= n => size (take n s) = if n < size s then n else size s.
proof. by elim s n => //=; smt. qed.

lemma take_cat n (s1 s2 : 'a list):
   take n (s1 ++ s2) =
     if n < size s1 then take n s1 else s1 ++ take (n - size s1) s2.
proof. by elim s1 n => //=; smt. qed.

lemma take_size_cat n (s1 s2 : 'a list):
  size s1 = n => take n (s1 ++ s2) = s1.
proof. by intros=> <-; rewrite take_cat subzz ltzz take0 cats0. qed.

lemma cat_take_drop n (s : 'a list): take n s ++ drop n s = s.
proof. by elim s n; smt. qed.

lemma nth_drop (x0 : 'a) n s i:
  0 <= n => 0 <= i => nth x0 (drop n s) i = nth x0 s (n + i).
proof.
  intros=> n_ge0 i_ge0; case (n < size s) => [lt_n_s|le_s_n]; last smt.
  rewrite -{2}(cat_take_drop n s) nth_cat size_take //; smt.
qed.

lemma nth_take (x0 : 'a) n s i:
  0 <= n => 0 <= i => nth x0 (drop n s) i = nth x0 s (n + i).
proof.
  intros=> n_ge0 i_ge0; case (n < size s) => [lt_n_s|le_s_n]; last smt.
  rewrite -{2}(cat_take_drop n s) nth_cat size_take //; smt.
qed.

op catrev (s1 s2 : 'a list) =
  with s1 = "[]"      => s2
  with s1 = (::) x s1 => catrev s1 (x :: s2).

op rev (s : 'a list) = catrev s [].

lemma catrev_catl (s t u : 'a list):
  catrev (s ++ t) u = catrev t (catrev s u).
proof. by elim s u => //= x s h u; rewrite h. qed.

lemma catrev_catr (s t u : 'a list):
  catrev s (t ++ u) = catrev s t ++ u.
proof. by elim s t => //= x s IHs t; rewrite -IHs. qed.

lemma catrevE (s t : 'a list): catrev s t = rev s ++ t.
proof. by rewrite /rev -catrev_catr. qed.

lemma rev_nil: rev [<:'a>] = [].
proof. by rewrite /rev. qed.

lemma rev_cons (x : 'a) s: rev (x :: s) = rcons (rev s) x.
proof. by rewrite -cats1 -catrevE. qed.

lemma size_rev (s : 'a list): size (rev s) = size s.
proof.
  elim s; first by rewrite /rev.
  by intros=> x s IHs; rewrite rev_cons size_rcons IHs /=; smt.
qed.

lemma rev_cat (s t : 'a list): rev (s ++ t) = rev t ++ rev s.
proof. by rewrite /rev -catrev_catr /= -catrev_catl. qed.

lemma rev_rcons s (x : 'a): rev (rcons s x) = x :: rev s.
proof. by rewrite -cats1 rev_cat /rev /=. qed.

lemma revK (s : 'a list): rev (rev s) = s.
proof. by elim s; smt. qed.

op map (f : 'a -> 'b) xs =
  with xs = "[]"      => []
  with xs = (::) y ys => (f y) :: (map f ys).

lemma map_cons (f : 'a -> 'b) x s: map f (x :: s) = f x :: map f s.
proof. by []. qed.

lemma map_cat (f : 'a -> 'b) s1 s2:
  map f (s1 ++ s2) = map f s1 ++ map f s2.
proof. by elim s1 => [|x s1 IHs] //=; rewrite IHs. qed.

lemma size_map (f : 'a -> 'b) s: size (map f s) = size s.
proof. by elim s => [// | x s /= ->]. qed.

lemma nth_map x1 x2 (f : 'a -> 'b) n s:
  0 <= n < size s => nth x2 (map f s) n = f (nth x1 s n).
proof. by elim s n; smt. qed.

lemma map_rcons (f : 'a -> 'b) s x:
  map f (rcons s x) = rcons (map f s) (f x).
proof. by rewrite -!cats1 map_cat. qed.

lemma last_map (f : 'a -> 'b) s x:
  last_ (f x) (map f s) = f (last_ x s).
proof. by elim s x => //= x s ->. qed.

lemma filter_map (f : 'a -> 'b) p s:
  filter p (map f s) = map f (filter (preim f p) s).
proof.
  by elim s => //= x s IHs; rewrite (fun_if (map f)) /= IHs.
qed.

lemma has_map (f : 'a -> 'b) p s:
  has p (map f s) = has (preim f p) s.
proof. by elim s => //= x s ->. qed.

lemma all_map (f :  'a -> 'b) p s:
  all p (map f s) = all (preim f p) s.
proof. by elim s => //= x s ->. qed.

lemma count_map (f : 'a -> 'b) p s:
  count p (map f s) = count (preim f p) s.
proof. by elim s => //= x s ->. qed.

lemma map_take (f : 'a -> 'b) n s:
  map f (take n s) = take n (map f s).
proof.
  elim s n => //= x s IHs n.
  by case (n <= 0) => // _; rewrite IHs.
qed.

lemma map_drop (f : 'a -> 'b) n s:
  map f (drop n s) = drop n (map f s).
proof.
  elim s n => //= x s IHs n.
  by case (n <= 0) => // _; rewrite IHs.
qed.

lemma map_rev (f : 'a -> 'b) s:
  map f (rev s) = rev (map f s).
proof. elim s; first by rewrite rev_nil. smt. qed.

op foldr (f : 'a -> 'b -> 'b) z0 xs =
  with xs = "[]"      => z0
  with xs = (::) y ys => f y (foldr f z0 ys).

op flatten ['a] = foldr (++) [<:'a>].

op path (e : 'a -> 'a -> bool) (x : 'a) (p : 'a list) : bool =
  with p = "[]"      => true
  with p = (::) y p' => e x y /\ path e y p'.

op sorted (e : 'a -> 'a -> bool) (xs : 'a list) =
  with xs = "[]"      => true
  with xs = (::) y ys => false. (* BUG: path e y ys. *) 

op sort : ('a -> 'a -> bool) -> 'a list -> 'a list.

axiom sort_sorted (e : 'a -> 'a -> bool) (xs : 'a list):
     (forall x y, e x y || e y x)
  => sorted e (sort e xs).

axiom perm_sort (e : 'a -> 'a -> bool) (xs : 'a list):
     (forall x y, e x y || e y x)
  => perm_eq (sort e xs) xs.

op lex (e : 'a -> 'a -> bool) s1 s2 =
  with s1 = "[]"      , s2 = "[]"       => false
  with s1 = "[]"      , s2 = (::) y2 s2 => true
  with s1 = (::) y1 s1, s2 = "[]"       => false
  with s1 = (::) y1 s1, s2 = (::) y2 s2 =>
    if e y1 y2 then true else false.
