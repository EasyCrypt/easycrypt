(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* This API has been mostly inspired from the [seq] library of the
 * ssreflect Coq extension. *)

(* -------------------------------------------------------------------- *)
require import Fun Pred Option Pair Int IntExtra.

(* -------------------------------------------------------------------- *)
type 'a list = [
  | "[]"
  | (::) of  'a & 'a list
].

op size (xs : 'a list) =
  with xs = []      => 0
  with xs = y :: ys => 1 + (size ys).

lemma size_ge0 (s : 'a list): 0 <= size s.
proof. by elim s => //= x s; smt. qed.

lemma size_eq0 (s : 'a list): (size s = 0) <=> (s = []).
proof. by case s => //=; smt. qed.

(* -------------------------------------------------------------------- *)
lemma eqseq_cons (x1 x2 : 'a) (s1 s2 : 'a list) :
  (x1 :: s1 = x2 :: s2) <=> (x1 = x2) /\ (s1 = s2).
proof. by []. qed.

(* -------------------------------------------------------------------- *)
op head (z0 : 'a) (s : 'a list) =
  with s = []     => z0
  with s = x :: s => x.

lemma head_nil (z0 : 'a): head z0 [] = z0.
proof. by []. qed.

lemma head_cons (z0 : 'a) x s: head z0 (x :: s) = x.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
op ohead (s : 'a list) =
  with s = []     => None
  with s = x :: s => Some x.

lemma ohead_nil: ohead [<:'a>] = None.
proof. by []. qed.

lemma ohead_cons (x : 'a) s: ohead (x :: s) = Some x.
proof. by []. qed.

lemma head_ohead z0 (s : 'a list):
  head z0 s = odflt z0 (ohead s).
proof. by case: s. qed.

lemma ohead_head z0 (s : 'a list): s <> [] =>
  ohead s = Some (head z0 s).
proof. by case: s. qed.

(* -------------------------------------------------------------------- *)
op behead (xs : 'a list) =
  with xs = []      => []
  with xs = y :: ys => ys.

lemma behead_nil: behead [<:'a>] = [].
proof. by []. qed.

lemma behead_cons (x : 'a) xs: behead (x :: xs) = xs.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
lemma head_behead (xs : 'a list) z0:
  xs <> [] =>
  (head z0 xs) :: (behead xs) = xs.
proof. by elim xs. qed.

(* -------------------------------------------------------------------- *)
op nseq (n : int) (x : 'a) = iter n ((::) x) [].

lemma size_nseq n (x : 'a) : size (nseq n x) = max 0 n.
proof.
elim/natind: n => [n le0n|n ge0n ih] @/nseq.
  by rewrite iter0 // max_lel.
by rewrite iterS //= ih !max_ler 1?addzC // addz_ge0.
qed.

lemma nseq0 (x : 'a): nseq 0 x = [].
proof. by rewrite iter0. qed.

lemma nseq0_le n (x : 'a) : n <= 0 => nseq n x = [].
proof. by move=> le0_n; rewrite iter0. qed.

lemma nseqS n (x : 'a) : 0 <= n => nseq (n+1) x = x :: nseq n x.
proof. by move=> le0_n; rewrite iterS. qed.

(* -------------------------------------------------------------------- *)
(*                    Sequence catenation "cat"                         *)
(* -------------------------------------------------------------------- *)
op (++) (s1 s2 : 'a list) =
  with s1 = []      => s2
  with s1 = x :: s1 => x :: (s1 ++ s2).

op rcons (s : 'a list) (z : 'a) =
  with s = []      => [z]
  with s = x :: s' => x :: (rcons s' z).

op last (x : 'a) s =
  with s = []      => x
  with s = y :: ys => last y ys.

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

lemma eqseq_cat (s1 s2 s3 s4 : 'a list) : size s1 = size s2 =>
  (s1 ++ s3 = s2 ++ s4) <=> (s1 = s2) /\ (s3 = s4).
proof.
elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; rewrite ?(addz_neq0, size_ge0) //.
by move/addzI/ih=> ->.
qed.

lemma lastcons (x y : 'a) (s : 'a list): last x (y :: s) = last y s.
proof. by []. qed.

lemma lastcat (x : 'a) (s1 s2 : 'a list):
  last x (s1 ++ s2) = last (last x s1) s2.
proof. by elim s1 x=> //= x s1 ->. qed.

lemma lastrcons (x y : 'a) (s : 'a list): last x (rcons s y) = y.
proof. by elim s x=> //= x s ->. qed.

lemma lastnonempty (x1 x2 : 'a) (s : 'a list):
  s <> [] =>
  last x1 s = last x2 s.
proof. by case s. qed.

lemma size_rcons s (x : 'a):
  size (rcons s x) = (size s) + 1.
proof. by rewrite -cats1 size_cat /=. qed.

lemma cat_rcons (x : 'a) s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
proof. by rewrite -cats1 -catA. qed.

lemma rcons_cat (x : 'a) s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
proof. by rewrite -!cats1 catA. qed.

(* -------------------------------------------------------------------- *)
(*                   rcons / induction principle                        *)
(* -------------------------------------------------------------------- *)
lemma nosmt last_ind (p : 'a list -> bool):
  p [] => (forall s x, p s => p (rcons s x)) => forall s, p s.
proof.
  move=> Hnil Hlast s; rewrite -(cat0s s).
  elim s [] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
  by rewrite -cat_rcons (IHs (rcons s1 x)) // Hlast.
qed.

(* -------------------------------------------------------------------- *)
(*                        Sequence indexing                             *)
(* -------------------------------------------------------------------- *)
op nth x (xs : 'a list) n : 'a =
  with xs = []      => x
  with xs = y :: ys => if n = 0 then y else (nth x ys (n-1)).

op onth (xs : 'a list) n : 'a option =
  with xs = []      => None
  with xs = y :: ys =>  if n = 0 then Some y else (onth ys (n-1)).

lemma nth_onth (z : 'a) xs n: nth z xs n = odflt z (onth xs n).
proof. by elim xs n => //=; smt. qed.

lemma onth_nth (z : 'a) xs n:
  0 <= n < size xs => onth xs n = Some (nth z xs n).
proof. by elim xs n => //=; smt. qed.

lemma nth_default (z : 'a) s n: size s <= n => nth z s n = z.
proof.
  elim s n => //= x s IHs n; case (n = 0).
    by move=> ->; smt.
    by move=> _ _; rewrite IHs; smt.
qed.

lemma nth_neg (x0 : 'a) s n: n < 0 => nth x0 s n = x0.
proof. elim s n => //=; smt. qed.

lemma nth_out (x0 : 'a) s n: ! (0 <= n < size s) => nth x0 s n = x0.
proof.
rewrite anda_and -nand; case; rewrite (lezNgt, ltzNge) /=.
  by apply/nth_neg. by apply/nth_default.
qed.

lemma nth_cat (x0 : 'a) s1 s2 n:
  nth x0 (s1 ++ s2) n = if n < size s1 then nth x0 s1 n else nth x0 s2 (n - size s1).
proof.
  case (n < 0) => [n_lt0|n_ge0]; first by smt.
  by elim s1 n n_ge0; smt.
qed.

lemma nth_rcons x0 (s : 'a list) x n:
  nth x0 (rcons s x) n =
    if n < size s then nth x0 s n else if n = size s then x else x0.
proof. elim s n; smt. qed.

lemma eq_from_nth x0 (s1 s2 : 'a list):
     size s1 = size s2
  => (forall i, 0 <= i < size s1 => nth x0 s1 i = nth x0 s2 i)
  => s1 = s2.
proof.                        (* BUG: CHECKING IS TOO LONG *)
  elim s1 s2 => [|x1 s1 IHs1] [|x2 s2] //=; first 2 smt.
  move=> eq_szS h; cut eq_sz: size s1 = size s2 by smt.
  cut := h 0 => /= ->; first smt. rewrite (IHs1 s2) // => i le_i_s1.
  cut := h (i+1); smt.
qed.

(* -------------------------------------------------------------------- *)
(*                       Sequence membership                            *)
(* -------------------------------------------------------------------- *)
op mem (s : 'a list) (z : 'a) =
  with s = []      => false
  with s = x :: s' => (z = x) \/ mem s' z.

lemma in_nil (x : 'a): mem [] x = false.
proof. by []. qed.

lemma mem_eq0 (s : 'a list):
  (forall x, ! mem s x) => s = [].
proof. by case: s => [|x s] // h; have := h x. qed.

lemma in_nilE: mem [<:'a>] = pred0.
proof. by apply fun_ext. qed.

lemma in_cons y s (x : 'a): mem (y :: s) x <=> (x = y) \/ (mem s x).
proof. by []. qed.

lemma mem_head (x : 'a) s: mem (x :: s) x.
proof. by []. qed.

lemma mem_behead (s : 'a list):
  forall x, mem (behead s) x => mem s x.
proof. by move=> x; case: s => //= y s ->. qed.

lemma mem_head_behead z0 (s : 'a list):
  s <> [] =>
  forall x, (x = (head z0 s) \/ mem (behead s) x) <=> mem s x.
proof.
  move=> /head_behead h; rewrite -(h z0) head_cons behead_cons.
  by move=> x; rewrite in_cons.
qed.

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

lemma mem_cat (x : 'a) s1 s2:
  mem (s1 ++ s2) x <=> mem s1 x \/ mem s2 x.
proof. by elim s1 => //=; smt. qed.

lemma mem_rcons s (y : 'a):
  forall x, mem (rcons s y) x = mem (y :: s) x.
proof. by move=> x; rewrite -cats1 /= !mem_cat /= orbC. qed.

lemma mem_nth (x0 : 'a) s n : 0 <= n < size s => mem s (nth x0 s n).
proof. by elim: s n => [|x s ih] //= n; smt. qed.

(* -------------------------------------------------------------------- *)
(*                  find, filter, count, has, all                       *)
(* -------------------------------------------------------------------- *)
op find ['a] (p : 'a -> bool) s =
  with s = []      => 0
  with s = x :: s' => if p x then 0 else find p s' + 1.

op count ['a] (p : 'a -> bool) xs =
  with xs = []      => 0
  with xs = y :: ys => (b2i (p y)) + (count p ys).

op filter (p : 'a -> bool) xs =
  with xs = []      => []
  with xs = y :: ys => if p y then y :: filter p ys else filter p ys.

lemma count_ge0 (p : 'a -> bool) s: 0 <= count p s.
proof. by elim s=> //= x s; smt. qed.

lemma count_size p (s : 'a list): count p s <= size s.
proof. by elim s => //= x s; smt. qed.

op has (p : 'a -> bool) xs =
  with xs = []      => false
  with xs = y :: ys => (p y) \/ (has p ys).

op all (p : 'a -> bool) xs =
  with xs = []      => true
  with xs = y :: ys => (p y) /\ (all p ys).

lemma hasP p (s : 'a list): has p s <=> (exists x, mem s x /\ p x).
proof.
  elim s => //= y s IHs; case (p y) => py.
    by rewrite orTb /=; exists y; smt.
  by rewrite orFb IHs; split; elim=> x []; smt.
qed.

lemma hasPn (p : 'a -> bool) s :
  !has p s <=> (forall x, mem s x => !p x).
proof.
split=> [h x sx|h]; first apply: (contra _ _ _ h).
  by move=> px; apply/hasP; exists x.
by apply/negP=> /hasP [x [] /h].
qed.

lemma allP p (s : 'a list):
  all p s <=> (forall x, mem s x => p x).
proof.
  elim s=> //= x s [IH1 IH2]; split.
    by elim=> _ h y []; [move=> -> // | apply IH1].
  move=> h; split; [by apply h | apply IH2].
  by move=> y y_in_s; apply h; right.
qed.

lemma size_filter p (s : 'a list): size (filter p s) = count p s.
proof. by elim: s => //= x s; case: (p x) => _ ->. qed.

lemma filter_pred0 (s : 'a list): filter pred0 s = [].
proof. by elim s. qed.

lemma filter_predT (s : 'a list): filter predT s = s.
proof. by elim s => //= x s ->. qed.

lemma filter_predI (p1 p2 : 'a -> bool) (s : 'a list):
  filter (predI p1 p2) s = filter p1 (filter p2 s).
proof.
  elim s => //= x s IHs; rewrite IHs /predI.
  by case (p2 x) => //=; case (p1 x) => //=.
qed.

lemma count_filter p1 p2 (s : 'a list):
  count p1 (filter p2 s) = count (predI p1 p2) s.
proof. by rewrite -!size_filter filter_predI. qed.

lemma count_pred0 (s : 'a list): count pred0 s = 0.
proof. by rewrite -size_filter filter_pred0. qed.

lemma count_predT (s : 'a list): count predT s = size s.
proof. by rewrite -size_filter filter_predT. qed.

lemma count_predC p (s : 'a list):
  count p s + count (predC p) s = size s.
proof. elim s; smt. qed.

lemma has_nil p : has p [<:'a>] <=> false.
proof. by []. qed.

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

lemma all_predC p (s : 'a list): all (predC p) s = ! has p s.
proof. by elim s => //= x s ->; rewrite /predC; case (p x). qed.

lemma eq_filter p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => filter p1 s = filter p2 s.
proof. by move=> h; elim s=> //= x l; rewrite h=> ->. qed.

lemma eq_count p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => count p1 s = count p2 s.
proof. by move=> h; rewrite -!size_filter (eq_filter _ p2). qed.

lemma eq_has p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => has p1 s <=> has p2 s.
proof. by move=> h; rewrite !has_count (eq_count _ p2). qed.

lemma eq_all p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => all p1 s <=> all p2 s.
proof. by move=> h; rewrite !all_count (eq_count _ p2). qed.

lemma has_sym (s1 s2 : 'a list): has (mem s1) s2 <=> has (mem s2) s1.
proof. smt. qed.

lemma has_pred1 (z : 'a) s: has (pred1 z) s <=> mem s z.
proof. smt. qed.

lemma filter_all p (s : 'a list): all p (filter p s).
proof. by elim s => //= x s IHs; case (p x). qed.

lemma all_filterP p (s : 'a list): all p s <=> filter p s = s.
proof.
  split; last by move=> <-; apply filter_all.
  by elim s => //= x s IHs [-> Hs]; rewrite IHs.
qed.

lemma filter_id p (s : 'a list): filter p (filter p s) = filter p s.
proof. by apply all_filterP; apply filter_all. qed.

lemma filter_cat p (s1 s2 : 'a list): filter p (s1 ++ s2) = filter p s1 ++ filter p s2.
proof. by elim s1 => //= x s1 ->; case (p x). qed.

lemma filter_cons p x (s : 'a list):
  filter p (x :: s) = if p x then x :: filter p s else filter p s.
proof. by case: (p x)=> ->. qed.

lemma filter_rcons p x (s : 'a list):
  filter p (rcons s x) = if p x then rcons (filter p s) x else filter p s.
proof. by rewrite -!cats1 filter_cat; case: (p x)=> -> /=; rewrite ?cats0. qed.

lemma count_cat p (s1 s2 : 'a list): count p (s1 ++ s2) = count p s1 + count p s2.
proof. by rewrite -!size_filter filter_cat size_cat. qed.

lemma has_cat p (s1 s2 : 'a list): has p (s1 ++ s2) <=> has p s1 \/ has p s2.
proof. by elim s1 => //= x s1 IHs; rewrite IHs; smt. qed.

lemma all_cat p (s1 s2 : 'a list): all p (s1 ++ s2) <=> all p s1 /\ all p s2.
proof. by elim s1 => //= x s1 IHs; rewrite IHs. qed.

lemma mem_filter (p : 'a -> bool) x s:
  mem (filter p s) x <=> p x /\ (mem s x).
proof. by elim s => //= y s IHs; smt. qed.

lemma find_ge0 p (s : 'a list): 0 <= find p s.
proof. elim s; smt. qed.

lemma has_find p (s : 'a list): has p s <=> (find p s < size s).
proof. elim s; smt. qed.

lemma find_size p (s : 'a list): find p s <= size s.
proof. elim s; smt. qed.

lemma find_cat p (s1 s2 : 'a list):
  find p (s1 ++ s2) = if has p s1 then find p s1 else size s1 + find p s2.
proof. elim s1; smt. qed.

lemma nth_find z0 p (s : 'a list): has p s => p (nth z0 s (find p s)).
proof. elim s; smt. qed.

lemma filter_pred1 x (s : 'a list) :
  filter (pred1 x) s = nseq (count (pred1 x) s) x.
proof.
elim: s=> /= @/pred1 [|y s ih]; first by rewrite nseq0.
by case: (y = x)=> //; rewrite addzC nseqS ?count_ge0.
qed.

(* -------------------------------------------------------------------- *)
(*                              Lookup                                  *)
(* -------------------------------------------------------------------- *)
op index (x : 'a) = find (pred1 x).

lemma index_cons x y (s : 'a list):
  index x (y :: s) = if x = y then 0 else index x s + 1.
proof. by rewrite (eq_sym x y). qed.

lemma index_ge0 x (s : 'a list): 0 <= index x s.
proof. by rewrite /index find_ge0. qed.

lemma index_size x (s : 'a list): index x s <= size s.
proof. by rewrite /index find_size. qed.

lemma index_mem x (s : 'a list): (index x s < size s) = (mem s x).
proof. by rewrite -has_pred1 has_find. qed.

lemma nth_index z0 x (s : 'a list): mem s x => nth z0 s (index x s) = x.
proof.
  rewrite -has_pred1 => h; apply (nth_find z0 (pred1 x)) in h.
  by move: h; rewrite /pred1 => {2}<-.
qed.

lemma index_cat x (s1 s2 : 'a list):
 index x (s1 ++ s2) = if mem s1 x then index x s1 else size s1 + index x s2.
proof. by rewrite /index find_cat has_pred1. qed.

lemma index_head x (s : 'a list): index x (x :: s) = 0.
proof. by []. qed.

(* -------------------------------------------------------------------- *)
(*                            drop, take                                *)
(* -------------------------------------------------------------------- *)
op drop n (xs : 'a list) =
  with xs = []      => []
  with xs = y :: ys =>
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
proof. by move=> <-; rewrite drop_cat subzz ltzz drop0. qed.

lemma drop_nth (z0 : 'a) n s: 0 <= n < size s =>
  drop n s = nth z0 s n :: drop (n+1) s.
proof.
  elim: s n=> [|x s ih] n []; 1: by elim: n => [|n _] hn //=; 1: smt.
  by elim: n => [|n ge0_n _] /=; rewrite ?drop0 //= smt.
qed.

op take n (xs : 'a list) =
  with xs = []      => []
  with xs = y :: ys =>
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
proof. by move=> <-; rewrite take_cat subzz ltzz take0 cats0. qed.

lemma take_nth (z0 : 'a) n s: 0 <= n < size s =>
  take (n+1) s = rcons (take n s) (nth z0 s n).
proof.
  elim: s n=> [|x s ih] n []; 1: by elim: n => [|n _] hn //=; 1: smt.
  by elim: n => [|n ge0_n _] /=; rewrite ?take0 //= smt.
qed.

lemma cat_take_drop n (s : 'a list): take n s ++ drop n s = s.
proof. by elim s n; smt. qed.

lemma nth_drop (x0 : 'a) n s i:
  0 <= n => 0 <= i => nth x0 (drop n s) i = nth x0 s (n + i).
proof.
  move=> n_ge0 i_ge0; case (n < size s) => [lt_n_s|le_s_n]; last smt.
  rewrite -{2}(cat_take_drop n s) nth_cat size_take //; smt.
qed.

lemma nth_take (x0 : 'a) n s i:
  0 <= n => i < n => nth x0 (take n s) i = nth x0 s i.
proof.
  move=> n_ge0 i_ge0; case (n < size s) => [lt_n_s|le_s_n]; last smt.
  by rewrite -{2}(cat_take_drop n s) nth_cat size_take //; smt.
qed.

lemma splitPr (xs : 'a list) (x : 'a): mem xs x =>
  exists s1, exists s2, xs = s1 ++ x :: s2.
proof.
  move=> x_in_xs; pose i := index x xs.
  have lt_ip: i < size xs by rewrite /i index_mem.
  exists (take i xs); exists (drop (i+1) xs).
  rewrite -{1}(@cat_take_drop i) -(@nth_index x x xs) //.
  by rewrite -drop_nth // index_ge0 lt_ip.
qed.

(* -------------------------------------------------------------------- *)
(*                          Sequence shift                              *)
(* -------------------------------------------------------------------- *)
op rot n (s : 'a list) = drop n s ++ take n s.

lemma rot0 (s : 'a list): rot 0 s = s.
proof. smt. qed.

lemma rot_neg n (s : 'a list): n < 0 => rot n s = s.
proof. by move=> lt0_n; rewrite /rot !(drop_neg, take_neg) // cats0. qed.

lemma size_rot n (s : 'a list): size (rot n s) = size s.
proof. smt. qed.

lemma rot_oversize n (s : 'a list): size s <= n => rot n s = s.
proof. smt. qed.

lemma rot_size (s : 'a list): rot (size s) s = s.
proof. by apply rot_oversize. qed.

lemma has_rot n (s : 'a list) p: has p (rot n s) = has p s.
proof. by rewrite /rot has_cat orbC -has_cat cat_take_drop. qed.

lemma rot_size_cat (s1 s2 : 'a list): rot (size s1) (s1 ++ s2) = s2 ++ s1.
proof. by rewrite /rot take_size_cat ?drop_size_cat. qed.

lemma mem_rot n (s : 'a list): forall x, mem (rot n s) x <=> mem s x.
proof.
  by move=> x; rewrite -{2}(cat_take_drop n s) /rot !mem_cat orbC.
qed.

op rotr n (s : 'a list) = rot (size s - n) s.

lemma rotK n: cancel<:'a list, 'a list> (rot n) (rotr n).
proof. smt. qed.

lemma rot_inj n (s1 s2 : 'a list): rot n s1 = rot n s2 => s1 = s2.
proof. by apply (can_inj (rot n) (rotr n)); apply rotK. qed.

lemma rot1_cons x (s : 'a list): rot 1 (x :: s) = rcons s x.
proof. by rewrite /rot /= take0 drop0 -cats1. qed.

lemma rot_to (s : 'a list) x:
  mem s x => exists i s', rot i s = x :: s'.
proof.
  move=> s_x; pose i := index x s.
  exists i; exists (drop (i + 1) s ++ take i s).
  rewrite -cat_cons /i /rot => {i}; congr=> //=.
  elim s s_x => //= y s IHs; case (x = y); smt.
qed.

(* -------------------------------------------------------------------- *)
(*                    Equality up to permutation                        *)
(* -------------------------------------------------------------------- *)
op perm_eq ['a] (s1 s2 : 'a list) =
  all (fun x, count (pred1 x) s1 = count (pred1 x) s2) (s1 ++ s2).

lemma perm_eqP (s1 s2 : 'a list):
  perm_eq s1 s2 <=> (forall p, count p s1 = count p s2).
proof.
  rewrite /perm_eq allP /=; split; last by move=> h x _; apply h.
  move=> eq_cnt1 a; cut ltzSz: forall z, z < z + 1 by smt.
  (* FIX: negative occurence selector *)
  cut {ltzSz} := ltzSz (count a (s1 ++ s2)); move: {1 3 4}a.
  pose x := _ + 1; cut : 0 <= x by smt. move: x => {a}.
  elim; first by smt.
  move=> i i_ge0 IHi a le_ai; case (count a (s1 ++ s2) = 0).
    by rewrite count_cat; smt.
  rewrite neq_ltz ltzNge count_ge0 /=; rewrite -has_count hasP.
  case=> x [s12x a_x]; pose a' := predD1 a x.
  cut cnt_a': forall s, count a s = count (pred1 x) s + count a' s.
    move=> s; rewrite -size_filter -(count_predC (pred1 x)).
    rewrite  -2!size_filter -!filter_predI !size_filter.
    by congr; apply eq_count => y; delta.
  by rewrite !cnt_a' (eq_cnt1 x) // (IHi a') //; smt.
qed.

lemma perm_eq_refl (s : 'a list): perm_eq s s.
proof. by apply perm_eqP. qed.

lemma perm_eq_refl_eq (s1 s2 : 'a list):
  s1 = s2 => perm_eq s1 s2.
proof. by move=> ->; apply/perm_eq_refl. qed.

lemma perm_eq_sym (s1 s2 : 'a list): perm_eq s1 s2 <=> perm_eq s2 s1.
proof. by rewrite !perm_eqP; smt. qed.

lemma perm_eq_trans (s2 s1 s3 : 'a list):
  perm_eq s1 s2 => perm_eq s2 s3 => perm_eq s1 s3.
proof. by rewrite !perm_eqP => h1 h2 p; rewrite h1 h2. qed.

lemma perm_eqlP (s1 s2 : 'a list):
  perm_eq s1 s2 <=> (forall s, perm_eq s1 s <=> perm_eq s2 s).
proof.
  split; last by move=> ->; rewrite perm_eq_refl.
  move=> h s; split; last by apply perm_eq_trans.
  by apply perm_eq_trans; apply perm_eq_sym.
qed.

lemma perm_eqlE (s1 s2 : 'a list):
  perm_eq s1 s2 => forall s, perm_eq s1 s <=> perm_eq s2 s.
proof. by move=> h; apply perm_eqlP. qed.

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

lemma perm_catAC (s1 s2 s3 : 'a list):
  forall s, perm_eq ((s1 ++ s2) ++ s3) s <=> perm_eq ((s1 ++ s3) ++ s2) s.
proof. by rewrite -perm_eqlP -!catA perm_cat2l perm_catCl perm_eq_refl. qed.

lemma perm_catCA (s1 s2 s3 : 'a list):
  forall s, perm_eq (s1 ++ s2 ++ s3) s <=> perm_eq (s2 ++ s1 ++ s3) s.
proof. by rewrite -perm_eqlP; rewrite perm_cat2r perm_catC. qed.

lemma perm_consCA (x y : 'a) s:
  forall s', perm_eq (x :: y :: s) s' <=> perm_eq (y :: x :: s) s'.
proof. by move=> s'; cut := perm_catCA [x] [y] s s'. qed.

lemma perm_cons (x : 'a) s1 s2:
  perm_eq (x :: s1) (x :: s2) <=> perm_eq s1 s2.
proof. by move: (perm_cat2l [x]) => /= h; apply h. qed.

lemma perm_eq_mem (s1 s2 : 'a list):
  perm_eq s1 s2 => forall x, mem s1 x <=> mem s2 x.
proof. by rewrite perm_eqP => h x; rewrite -!has_pred1 !has_count h. qed.

lemma perm_eq_size (s1 s2 : 'a list):
  perm_eq s1 s2 => size s1 = size s2.
proof. by rewrite perm_eqP=> h; rewrite -!count_predT h. qed.

lemma perm_eq_small (s1 s2 : 'a list):
  size s2 <= 1 => perm_eq s1 s2 => s1 = s2.
proof.
  move=> s2_le1 eqs12; move: s2_le1 (perm_eq_mem s1 s2 _) => //.
  move: (perm_eq_size s1 s2 _) => // {eqs12}.
  case s2 => [|x []] //=; first last; last 2 smt.
  case s1 => [|y []] //=; last smt.
  by move=> h; cut := h x => /= ->.
qed.

lemma perm_eq_filter (p : 'a -> bool) (s1 s2 : 'a list):
  perm_eq s1 s2 => perm_eq (filter p s1) (filter p s2).
proof.
  rewrite !perm_eqP=> peq_s1_s2 p'.
  rewrite -!size_filter -!filter_predI !size_filter.
  exact/peq_s1_s2.
qed.

lemma perm_filterC (p : 'a -> bool) s :
  perm_eq (filter p s ++ filter (predC p) s) s.
proof.
elim: s => //= x s ih; case: (p x)=> @/predC -> //=;
  last rewrite /= -cat1s catA perm_catCA /=.
by rewrite perm_cons. by rewrite perm_cons.
qed.

(* -------------------------------------------------------------------- *)
(*                         Element removal                              *)
(* -------------------------------------------------------------------- *)
op rem (z : 'a) s =
  with s = []      => []
  with s = x :: s' => if x = z then s' else x :: (rem z s').

lemma rem_id (z : 'a) s: ! mem s z => rem z s = s.
proof.
  elim s => //= y s IHs; rewrite -nor; elim.
  move=> neq_yz s_notin_z; rewrite IHs // (eq_sym y).
  by cut ->: (z = y) <=> false.
qed.

lemma perm_to_rem (z : 'a) s : mem s z => perm_eq s (z :: rem z s).
proof.
  elim s => //= y s IHs; rewrite eq_sym perm_eq_sym.
  rewrite -ora_or; elim; first by move=> -> /=; rewrite perm_eq_refl.
  rewrite -neqF => -> /= z_in_s; rewrite -(cat1s z) -(cat1s y) catA.
  by rewrite perm_catCAl /= perm_cons perm_eq_sym IHs.
qed.

lemma size_rem (x : 'a) s: mem s x => size (rem x s) = (size s) - 1.
proof.
  move=> h; apply perm_to_rem in h; apply perm_eq_size in h.
  by rewrite h; smt.
qed.

lemma mem_rem (x : 'a) (s : 'a list):
  forall y, mem (rem x s) y => mem s y.
proof.
  move=> y; elim: s=> [|z s ih] //=; case: (z = x).
    by move=> _ ->. by move=> _ [-> | /ih ->].
qed.

lemma all_rem p (x : 'a) (s : 'a list): all p s => all p (rem x s).
proof. by move=> /allP h; apply/allP=> y /mem_rem /h. qed.

(* -------------------------------------------------------------------- *)
(*                        Element insertion                             *)
(* -------------------------------------------------------------------- *)
op insert (x : 'a) (s : 'a list) (n : int) =
  take n s ++ x :: drop n s.

op trim (xs : 'a list) (n : int) =
  take n xs ++ (drop (n+1) xs).

(* -------------------------------------------------------------------- *)
lemma trim_neg (xs : 'a list) (n : int): n < 0 => trim xs n = xs.
proof. smt. qed.

lemma size_trim (xs : 'a list) (n : int): 0 <= n < size xs =>
  size (trim xs n) = size xs - 1.
proof. smt. qed.

lemma trim_head (x : 'a) (xs : 'a list):
  trim (x :: xs) 0 = xs.
proof. smt. qed.

lemma trim_tail (x : 'a) (xs : 'a list) (n : int): 0 <= n =>
  trim (x :: xs) (n+1) = x :: trim xs n.
proof. smt. qed.

lemma trim_cat (xs ys : 'a list) (n : int): n < size (xs ++ ys) =>
  trim (xs ++ ys) n =
    if   n < size xs
    then (trim xs n) ++ ys
    else xs ++ trim ys (n - size xs).
proof. by rewrite size_cat /trim; smt. qed.

(* -------------------------------------------------------------------- *)
(*                        Sequence reversal                             *)
(* -------------------------------------------------------------------- *)
op catrev (s1 s2 : 'a list) =
  with s1 = []      => s2
  with s1 = x :: s1 => catrev s1 (x :: s2).

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

lemma rev1 (x : 'a): rev [x] = [x].
proof. by []. qed.

lemma size_rev (s : 'a list): size (rev s) = size s.
proof.
  elim s; first by rewrite /rev.
  by move=> x s IHs; rewrite rev_cons size_rcons IHs /=; smt.
qed.

lemma rev_cat (s t : 'a list): rev (s ++ t) = rev t ++ rev s.
proof. by rewrite /rev -catrev_catr /= -catrev_catl. qed.

lemma rev_rcons s (x : 'a): rev (rcons s x) = x :: rev s.
proof. by rewrite -cats1 rev_cat /rev /=. qed.

lemma revK (s : 'a list): rev (rev s) = s.
proof. by elim s; smt. qed.

lemma rev_inj : injective rev<:'a>.
proof. by move=> s1 s2 /(congr1 rev); rewrite !revK. qed.

lemma catsI (s t1 t2 : 'a list): s ++ t1 = s ++ t2 => t1 = t2.
proof. by move=> h; have /eqseq_cat /= <-: size s = size s by done. qed.

lemma catIs (s1 s2 t : 'a list): s1 ++ t = s2 ++ t => s1 = s2.
proof. by move/(congr1 rev); rewrite !rev_cat => /catsI /rev_inj. qed.

lemma mem_rev (s : 'a list):
  forall x, mem (rev s) x = mem s x.
proof.
  move=> x; elim s; first by rewrite rev_nil.
  by move=> y s IHs; rewrite rev_cons mem_rcons /= IHs.
qed.

lemma filter_rev p (s : 'a list): filter p (rev s) = rev (filter p s).
proof.
  elim: s => /= [|x s ih]; rewrite ?rev_nil // fun_if.
  by rewrite !rev_cons filter_rcons ih.
qed.

lemma count_rev p (s : 'a list): count p (rev s) = count p s.
proof. by rewrite -!size_filter filter_rev size_rev. qed.

lemma has_rev p (s : 'a list): has p (rev s) = has p s.
proof. by rewrite !has_count count_rev. qed.

lemma all_rev p (s : 'a list): all p (rev s) = all p s.
proof. by rewrite !all_count count_rev size_rev. qed.

(* -------------------------------------------------------------------- *)
(*                        Duplicate-freenes                             *)
(* -------------------------------------------------------------------- *)
op uniq (s : 'a list) =
  with s = []      => true
  with s = x :: s' => !(mem s' x) /\ uniq s'.

lemma cons_uniq (x : 'a) s:
  uniq (x :: s) <=> (!mem s x) /\ uniq s.
proof. by []. qed.

lemma cat_uniq (s1 s2 : 'a list):
  uniq (s1 ++ s2) <=> uniq s1 /\ ! has (mem s1) s2 /\ uniq s2.
proof.
  elim s1 => [|x s1 IHs]; first by rewrite /= in_nilE has_pred0.
  by rewrite has_sym /= IHs has_sym mem_cat => {IHs}; smt.
qed.

lemma uniq_catC (s1 s2 : 'a list): uniq (s1 ++ s2) = uniq (s2 ++ s1).
proof. by rewrite !cat_uniq has_sym; smt. qed.

lemma uniq_catCA (s1 s2 s3 : 'a list):
  uniq (s1 ++ s2 ++ s3) <=> uniq (s2 ++ s1 ++ s3).
proof.
  by rewrite -!(uniq_catC s3) !(cat_uniq s3) uniq_catC !has_cat orbC.
qed.

lemma rcons_uniq s (x : 'a): uniq (rcons s x) <=> (!mem s x) /\ uniq s.
proof. by rewrite -cats1 uniq_catC /=. qed.

lemma filter_uniq (s : 'a list) p: uniq s => uniq (filter p s).
proof. by elim s => //=; smt. qed.

lemma rot_uniq n (s : 'a list): uniq (rot n s) = uniq s.
proof. by rewrite /rot uniq_catC cat_take_drop. qed.

lemma rev_uniq (s : 'a list): uniq (rev s) <=> uniq s.
proof.
  elim s => /=; [by rewrite rev_nil | move=> x s IHs].
  by rewrite rev_cons -cats1 cat_uniq IHs /= mem_rev.
qed.

lemma rem_filter x (s : 'a list): uniq s =>
  rem x s = filter (predC1 x) s.
proof.
  elim s => //= y s ih [y_notin_s /ih->]; rewrite /predC1.
  case (y = x)=> //= <-; apply/eq_sym/all_filterP.
  (* FIXME: non genuine unification failure *)
     cut := all_predC (fun z => z = y) s => ->.
  by cut := has_pred1 y => ->.
qed.

lemma index_uniq z0 i (s : 'a list):
  0 <= i < size s => uniq s => index (nth z0 s i) s = i.
proof. by elim: s i; smt. qed.

lemma rem_uniq x s: uniq<:'a> s => uniq (rem x s).
proof.                          (* FIXME: subseq *)
  elim: s=> [|y s ih] //= [y_notin_s uq_s].
  case: (y = x)=> // ne_xy; rewrite ih //=.
  by move: y_notin_s; apply/contra => /mem_rem.
qed.

(* -------------------------------------------------------------------- *)
(*                       Removing duplicates                            *)
(* -------------------------------------------------------------------- *)
op undup (s : 'a list) =
  with s = []      => []
  with s = x :: s' => if mem s' x then undup s' else x :: undup s'.

lemma size_undup (s : 'a list): size (undup s) <= size s.
proof. by elim s => //= x s IHs; smt. qed.

lemma mem_undup (s : 'a list): forall x, mem (undup s) x = mem s x.
proof. move=> x; elim s => //= y s IHs; smt. qed.

lemma undup_uniq (s : 'a list): uniq (undup s).
proof. by elim s => //= x s IHs; case (mem s x); smt. qed.

lemma undup_id (s : 'a list): uniq s => undup s = s.
proof. by elim s => //= x s IHs; smt. qed.

lemma count_uniq_mem s (x : 'a):
  uniq s => count (pred1 x) s = b2i (mem s x).
proof. elim s; smt. qed.

lemma uniq_leq_size (s1 s2 : 'a list):
  uniq s1 => (mem s1 <= mem s2) => size s1 <= size s2.
proof.                          (* FIXME: test case for views *)
  rewrite /Pred.(<=); elim s1 s2 => //.
    by move=> s2 /=; rewrite size_ge0.
  move=> x s1 IHs s2 [not_s1x Us1]; rewrite -(allP (mem s2)) /=.
  case=> s2x; rewrite allP => ss12; cut := rot_to s2 x _ => //.
  case=> i s3 def_s2; rewrite -(size_rot i s2) def_s2 /= lez_add2l.
  apply IHs => // y s1y; cut := ss12 y _ => //.
  by rewrite -(mem_rot i) def_s2; case.
qed.

lemma leq_size_uniq (s1 s2 : 'a list):
  uniq s1 => (mem s1 <= mem s2) => size s2 <= size s1 => uniq s2.
proof.
  rewrite /Pred.(<=); elim s1 s2 => [[] | x s1 IHs s2] //; first smt.
  move=> Us1x; cut [not_s1x Us1] := Us1x; rewrite -(allP (mem s2)).  
  case=> s2x; rewrite allP => ss12 le_s21.
  cut := rot_to s2 x _ => //; case=> {s2x} i s3 def_s2.
  move: le_s21; rewrite -(rot_uniq i) -(size_rot i) def_s2 /= lez_add2l => le_s31.
  cut ss13: forall y, mem s1 y => mem s3 y.
    move=> y s1y; cut := ss12 y _ => //.
    by rewrite -(mem_rot i) def_s2 in_cons; case=> // eq_yx.
  rewrite IHs //=; move: le_s31; apply contraL; rewrite -ltzNge => s3x.
  rewrite -lez_add1r; cut := uniq_leq_size (x::s1) s3 _ => //= -> //.
  by apply (allP (mem s3)); rewrite /= s3x /= allP.
qed.

lemma uniq_size_uniq (s1 s2 : 'a list):
     uniq s1 => (forall x, mem s1 x <=> mem s2 x)
  => uniq s2 <=> (size s2 = size s1).
proof.
  move=> Us1 eqs12; split=> [Us2 | eq_sz12].
    by rewrite eqz_leq !uniq_leq_size // => y; rewrite eqs12.
  apply (leq_size_uniq s1) => //; first by move=> x; rewrite eqs12.
  by rewrite eq_sz12 lezz.
qed.

lemma leq_size_perm (s1 s2 : 'a list):
    uniq s1 => (mem s1 <= mem s2) => size s2 <= size s1
  => (forall x, mem s1 x <=> mem s2 x) /\ (size s1 = size s2).
proof.
  move=> Us1 ss12 le_s21; cut Us2 := leq_size_uniq s1 s2 _ _ _ => //.
  rewrite -anda_and; split=> [|h]; last by rewrite eq_sym -uniq_size_uniq.
  move=> x; split; [by apply ss12 | move=> s2x; move: le_s21].
  apply absurd => not_s1x; rewrite -ltzNge -lez_add1r.
  cut := uniq_leq_size (x :: s1) => /= -> //=.
  by rewrite /Pred.(<=) -(allP (mem s2)) /= s2x /= allP.
qed.

lemma perm_uniq (s1 s2 : 'a list):
     (forall x, mem s1 x <=> mem s2 x) => size s1 = size s2
  => uniq s1 <=> uniq s2.
proof.
  move=> Es12 Hs12; split=> Us.
  by rewrite (uniq_size_uniq s1) // eq_sym.
  by rewrite (uniq_size_uniq s2) // => y; rewrite Es12.
qed.

lemma perm_eq_uniq (s1 s2 : 'a list):
  perm_eq s1 s2 => uniq s1 <=> uniq s2.
proof.
  move=> eq_s12; apply perm_uniq;
    [by apply perm_eq_mem | by apply perm_eq_size].
qed.

lemma uniq_perm_eq (s1 s2 : 'a list):
  uniq s1 => uniq s2 => (forall x, mem s1 x <=> mem s2 x) => perm_eq s1 s2.
proof.
  move=> Us1 Us2 eq12; rewrite /perm_eq allP => x _ /=.
  by rewrite !count_uniq_mem // eq12.
qed.

lemma count_mem_uniq (s : 'a list):
  (forall x, count (pred1 x) s = b2i (mem s x)) => uniq s.
proof.
  move=> count1_s; cut Uus := undup_uniq s.
  apply (perm_eq_uniq (undup s)); last by apply undup_uniq.
  rewrite /perm_eq allP => x _ /=; rewrite count1_s.
  by rewrite (count_uniq_mem (undup s) x) ?undup_uniq // mem_undup.
qed.

(* -------------------------------------------------------------------- *)
(*                             Mapping                                  *)
(* -------------------------------------------------------------------- *)
op map (f : 'a -> 'b) xs =
  with xs = []      => []
  with xs = y :: ys => (f y) :: (map f ys).

lemma eq_map (f1 f2 : 'a -> 'b):
     (forall x, f1 x = f2 x)
  => forall s, map f1 s = map f2 s.
proof. by move=> Ef; elim=> //= x s ->; rewrite Ef. qed.

lemma map_f (f : 'a -> 'b) s x: mem s x => mem (map f s) (f x).
proof. by elim: s => [|y s ih] //=; case=> [| /ih] ->. qed.

lemma mapP ['a 'b] (f : 'a -> 'b) s y:
  mem (map f s) y <=> (exists x, mem s x /\ y = f x).
proof.
  elim: s => [|x s ih] //=; case: (y = f x)=> //=.
    by move=> ->; exists x.
  move=> ne_yfx; split; 1: move/ih.
    by case=> x' [hx' ->]; exists x'; rewrite hx'.
  case=> x' [h ->>]; case: h; 1: by move=> ->>; move: ne_yfx.
  by move=> x'_in_s; apply/ih; exists x'.
qed.

lemma mem_map ['a 'b] (f : 'a -> 'b) : injective f =>
  forall s x, (mem (map f s) (f x)) <=> (mem s x).
proof.
move=> inj_f s x; split=> [/mapP|].
  by case=> y [_ /inj_f]. by apply/map_f.
qed.

lemma uniq_map (f : 'a -> 'b) (s : 'a list):
  uniq (map f s) => uniq s.
proof.
  elim: s=> //= x s ih [x1_notin_fs /ih] -> /=.
  by apply/not_def=> /(map_f f).
qed.

lemma map_cons (f : 'a -> 'b) x s: map f (x :: s) = f x :: map f s.
proof. by []. qed.

lemma map_cat (f : 'a -> 'b) s1 s2:
  map f (s1 ++ s2) = map f s1 ++ map f s2.
proof. by elim s1 => [|x s1 IHs] //=; rewrite IHs. qed.

lemma size_map (f : 'a -> 'b) s: size (map f s) = size s.
proof. by elim s => [// | x s /= ->]. qed.

lemma map_comp (f1 : 'b -> 'c) (f2 : 'a -> 'b) s:
  map (f1 \o f2) s = map f1 (map f2 s).
proof. by elim: s => //= x s ->. qed.

lemma map_id (s : 'a list): map idfun s = s.
proof. by elim: s => //= x s ->. qed.

lemma id_map f (s : 'a list): (forall x, f x = x) => map f s = s.
proof. by move=> h; rewrite -{2}(@map_id s); apply/eq_map. qed.

lemma nth_map x1 x2 (f : 'a -> 'b) n s:
  0 <= n < size s => nth x2 (map f s) n = f (nth x1 s n).
proof. by elim s n; smt. qed.

lemma onth_nth_map (s : 'a list) n: onth s n = nth None (map Some s) n.
proof. by elim s n; smt. qed.

lemma map_rcons (f : 'a -> 'b) s x:
  map f (rcons s x) = rcons (map f s) (f x).
proof. by rewrite -!cats1 map_cat. qed.

lemma last_map (f : 'a -> 'b) s x:
  last (f x) (map f s) = f (last x s).
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

lemma perm_eq_map (f : 'a -> 'b) (s1 s2 : 'a list):
  perm_eq s1 s2 => perm_eq (map f s1) (map f s2).
proof.
  move=> h; apply/perm_eqP=> p; rewrite !count_map.
  by apply/perm_eqP.
qed.

lemma map_inj_in_uniq (f : 'a -> 'b) s:
     (forall x y, mem s x => mem s y => f x = f y => x = y)
  => uniq (map f s) <=> uniq s.
proof.
  elim: s => // x s ih injf /=; rewrite ih /=.
    by move=> x' y' sx' sy'; apply/injf=> /=; rewrite ?(sx', sy').
  case: (uniq s) => //= uniq_s; split=> h; 2: by apply/map_f.
  move/mapP: h => [x'] [x'_in_s eq_fxx']; rewrite (@injf x x') //.
  by rewrite mem_behead.
qed.

lemma mem_map_fst (xs : ('a * 'b) list) (x : 'a):
  mem (map fst xs) x <=> (exists y, mem xs (x,y)).
proof.
  rewrite (@mapP fst); split; case=> [[x' y] [h ->]|y h].
    by exists y. by exists (x, y).
qed.

lemma mem_map_snd (xs : ('a * 'b) list) (y : 'b):
  mem (map snd xs) y <=> (exists x, mem xs (x,y)).
proof.
  rewrite (@mapP snd); split; case=> [[x y'] [h ->]|x h].
    by exists x. by exists (x, y).
qed.

lemma nth_index_map (z0 : 'a) (f : 'a -> 'b) (s : 'a list) x:
     (forall x y, mem s x => mem s y => f x = f y => x = y)
  => mem s x => nth z0 s (index (f x) (map f s)) = x.
proof.
  elim: s => //= y s ih inj_f s_x; rewrite index_cons.
  case: (f x = f y) => eqf /=; 1: by apply/eq_sym/inj_f.
  move: s_x eqf; case: (x = y)=> //= ne_xy s_x _.
  rewrite addz1_neq0 1:index_ge0 //= subzE -addzA /= ih //.
  by move=> x' y' s_x' s_y'; apply/inj_f; rewrite ?(s_x', s_y').
qed.

(* -------------------------------------------------------------------- *)
(*                         Partial mapping                              *)
(* -------------------------------------------------------------------- *)
op pmap ['a 'b] (f : 'a -> 'b option) (s : 'a list) =
  with s = []     => []
  with s = x :: s =>
    if f x = None then pmap f s else oget (f x) :: pmap f s.

(* -------------------------------------------------------------------- *)
(*                          Index sequence                              *)
(* -------------------------------------------------------------------- *)
theory Iota.
  op iota_ : int -> int -> int list.

  axiom iota0 i n : n <= 0 => iota_ i n = [].
  axiom iotaS i n : 0 <= n => iota_ i (n+1) = i :: iota_ (i+1) n.

  lemma iota1 i : iota_ i 1 = [i].
  proof. by rewrite (iotaS i 0) // iota0. qed.

  lemma size_iota m n: size (iota_ m n) = max 0 n.
  proof. 
    elim/natind: n m => [n hn|n hn ih] m.
      by rewrite iota0 // max_lel.
    rewrite iotaS //= ih max_ler // smt.
  qed.
 
  lemma iota_add m n1 n2 : 0 <= n1 => 0 <= n2 =>
     iota_ m (n1 + n2) = iota_ m n1 ++ iota_ (m + n1) n2.
  proof.
    move=> ge0_n1 ge0_n2; elim n1 ge0_n1 m => /= [|n1 ge0_n1 ih] m.
      by rewrite (iota0 m 0).
    by rewrite addzAC !iotaS // 1:smt ih addzAC addzA.
  qed.
 
  lemma iotaSr i n : 0 <= n =>
    iota_ i (n+1) = rcons (iota_ i n) (i+n).
  proof. by move=> ge0_n; rewrite iota_add // iota1 cats1. qed.

  lemma nth_iota m n i w: 0 <= i < n => nth w (iota_ m n) i = m + i.
  proof.
    case=> ge0_i lt_in; rewrite (_ : n = i + ((n-i-1)+1)) 1:smt.
    rewrite iota_add // 1:smt nth_cat size_iota max_ler //=.
    by rewrite iotaS // smt.
  qed.

  lemma iota_addl (m1 m2:int) n: iota_ (m1 + m2) n = map ((+) m1) (iota_ m2 n).
  proof.
    elim/natind: n m2 => [n hn|n hn ih] m2; 1: by rewrite !iota0.
    by rewrite !iotaS // map_cons -addzA ih.
  qed.
 
  lemma mem_iota m n i : mem (iota_ m n) i <=> (m <= i /\ i < m + n).
  proof.
    elim/natind: n m => [n hn|n hn ih] m.
      by rewrite iota0 // smt.  
    by rewrite iotaS // in_cons ih smt.
  qed.

  lemma iota_uniq m n : uniq (iota_ m n).
  proof.
    elim/natind: n m => [n hn|n hn ih] m.
      by rewrite iota0.
    by rewrite iotaS // cons_uniq mem_iota ih // smt.
  qed.

  lemma last_iota k m n:
    last k (Iota.iota_ m n) = if n <= 0 then k else m + n - 1.
  proof.
    elim/natind: n m k => [n hn|n hn ih] m k.
      by rewrite iota0 hn.
    by rewrite iotaS //= ih smt.
  qed.
end Iota.

export Iota.

(* -------------------------------------------------------------------- *)
theory Range.
  op range (m n : int) = iota_ m (n - m).

  import Ring.IntID.

  lemma range_geq (m n : int): n <= m => range m n = [].
  proof. smt. qed.

  lemma range_ltn (m n : int): m < n =>
    range m n = m :: range (m+1) n.
  proof. smt. qed.

  lemma rangeS (m : int): range m (m+1) = [m].
  proof. by rewrite range_ltn 1:smt range_geq. qed.

  lemma range_add (m n a : int):
    range (m+a) (n+a) = map (Int.(+) a) (range m n).
  proof. by rewrite /range addrC iota_addl; congr; smt. qed.

  lemma range_addl (m n a : int):
    range (m+a) n = map (Int.(+) a) (range m (n-a)).
  proof. by rewrite -{1}(addrNK a n) -subrE range_add. qed.

  lemma range_addr (m n a : int):
    range m (n+a) = map (Int.(+) a) (range (m-a) n).
  proof. by rewrite -{1}(addrNK a m) -subrE range_add. qed.

  lemma range_cat (n m p : int): m <= n => n <= p =>
    range m p = range m n ++ range n p.
  proof. 
    rewrite /range (_: p - m = n - m + (p - n)) 1:smt.
    by move=> le_mn le_np; rewrite iota_add; smt.
  qed.

  lemma rangeSr (n m:int): n <= m =>
    range n (m+1) = rcons (range n m) m.
  proof.
    move=> le_nk; rewrite -cats1 (range_cat m) ?rangeS //.
      by rewrite lez_addl.
  qed.

  lemma mem_range (m n i: int):
    (mem (range m n) i) <=> (m <= i < n).
  proof.
    rewrite /range mem_iota; case: (m <= i)=> //=.
    by rewrite subrE addrCA addrN addr0.
  qed.

  lemma range_uniq m n: uniq (range m n).
  proof. by apply/iota_uniq. qed.

  lemma size_range m n: size (range m n) = max 0 (n - m).
  proof. by apply/size_iota. qed.

  lemma nth_range  (i p k w : int):
    0 <= i < p - k => nth w (range k p) i = k + i.
  proof. by apply/nth_iota. qed.
end Range.

export Range.

(* -------------------------------------------------------------------- *)
(*                        Association lists                             *)
(* -------------------------------------------------------------------- *)
op assoc (xs : ('a * 'b) list) (a : 'a) =
  omap snd (onth xs (index a (map fst xs))).

lemma assoc_nil a: assoc [<:'a * 'b>] a = None.
proof. by []. qed.

lemma assoc_cons x y s a:
    assoc<:'a, 'b> ((x, y) :: s) a
  = if a = x then Some y else assoc s a.
proof.
  rewrite /assoc /= index_cons {1 3}/fst /=; case: (a = x)=> //=.
  by move=> _; rewrite subzE -addzA /=addz1_neq0 // index_ge0.
qed.

lemma assoc_head x y s: assoc<:'a, 'b> ((x, y) :: s) x = Some y.
proof. by rewrite assoc_cons. qed.

lemma assoc_cat (s1 s2 : ('a * 'b) list) x:
    assoc (s1 ++ s2) x
  = if mem (map fst s1) x then assoc s1 x else assoc s2 x.
proof.
  elim: s1 => /= [|[x' y'] s ih] //; rewrite !assoc_cons /=.
  by rewrite /(fst _) /=; case: (x = x').
qed.

lemma mem_assoc_uniq (s : ('a * 'b) list) (a : 'a) (b : 'b):
  uniq (map fst s) => mem s (a, b) <=> assoc s a = Some b.
proof.
  elim: s => //= [[x y]] s ih; rewrite eq_sym => [x_notin_1s uq_1s] /=.
  case: (x = a) => [->> |] /=; 1: rewrite assoc_head /=.
    by apply/eq_iff/orb_idr=> /(map_f fst); rewrite x_notin_1s.
  by move=> ne_xa; rewrite assoc_cons ih // (@eq_sym a) ne_xa.
qed.

lemma assocP (s : ('a * 'b) list) (x : 'a):
     (  mem (map fst s) x /\ exists y, mem s (x, y) /\ assoc s x = Some y)
  \/ (! mem (map fst s) x /\ assoc s x = None).
proof.
  elim: s=> //=; case=> x' y' s ih; rewrite /(fst (x', _)) /=.
  case: (x = x') => /= [<<- |]; 1: by exists y'; rewrite assoc_cons.
  by rewrite assoc_cons => ->.
qed.

lemma perm_eq_assoc (s1 s2 : ('a * 'b) list) x:
     uniq (map fst s2)
  => perm_eq s1 s2 => assoc s1 x = assoc s2 x.
proof.
  move=> uq_s1 peq_s1s2.
  case: (assocP s1 x); last first.
    case=> Ns1_x ->; case: (assocP s2 x); 2: by case=> _ <-.
    by have/perm_eq_mem <- := perm_eq_map fst _ _ peq_s1s2.
  case=> s1_x [y1 [s1_xy1 ->]]; apply/eq_sym.
  by rewrite -mem_assoc_uniq //; apply/(perm_eq_mem _ _ peq_s1s2).
qed.

lemma assoc_filter (p : 'a -> bool) (s : ('a * 'b) list) x:
  assoc (filter (p \o fst) s) x = if (p x) then assoc s x else None.
proof.
  elim: s=> //= [|[x' y'] s ih]; 1: by rewrite assoc_nil.
  rewrite assoc_cons; case: (x = x') => [<<- |ne_xx'].
    rewrite {1}/(\o) {1}/fst /=; case (p x).
    by rewrite assoc_cons. by rewrite ih=> ->.
  by case: ((\o) _ _ _)=> //=; rewrite assoc_cons ne_xx'.
qed.

(* -------------------------------------------------------------------- *)
(*         Sequence from a function computing from indexes              *)
(* -------------------------------------------------------------------- *)
op mkseq (f : int -> 'a) n = map f (iota_ 0 n).

lemma size_mkseq (f : int -> 'a) n: size (mkseq f n) = max 0 n.
proof. by rewrite /mkseq size_map size_iota. qed.

lemma eq_mkseq (f g : int -> 'a):
     (forall x, f x = g x)
  => forall n, mkseq f n = mkseq g n.
proof. by move=> Efg n; apply eq_map. qed.

lemma nth_mkseq x0 (f : int -> 'a) n i:
  0 <= i < n => nth x0 (mkseq f n) i = f i.
proof.
  by move=> Hi; rewrite /mkseq (nth_map 0) ?nth_iota ?size_iota; smt.
qed.

lemma mkseq_nth (x0 : 'a) s: mkseq (nth x0 s) (size s) = s.
proof.
  apply (eq_from_nth x0); rewrite size_mkseq; first smt.
  by move=> i Hi; rewrite nth_mkseq //; smt.
qed.

lemma mkseq0 (f : int -> 'a) : mkseq f 0 = [].
proof. by rewrite /mkseq iota0. qed.

(* -------------------------------------------------------------------- *)
(*                         Sequence folding                             *)
(* -------------------------------------------------------------------- *)
op foldr (f : 'a -> 'b -> 'b) z0 xs =
  with xs = []      => z0
  with xs = y :: ys => f y (foldr f z0 ys).

lemma foldr_cat (f : 'a -> 'b -> 'b) z0 s1 s2:
  foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
proof. by elim s1 => //= x s1 ->. qed.

lemma foldr_map ['a 'b 'c] (f : 'a -> 'b -> 'b) (h : 'c -> 'a) z0 s:
  foldr f z0 (map h s) = foldr (fun x z, f (h x) z) z0 s.
proof. by elim s => //= x s ->. qed.

op foldl (f : 'b -> 'a -> 'b) z0 xs =
  with xs = []      => z0
  with xs = y :: ys => foldl f (f z0 y) ys.

lemma foldl_rev (f : 'b -> 'a -> 'b) z0 s:
  foldl f z0 (rev s) = foldr (fun x z => f z x) z0 s.
proof.
  elim/last_ind s z0 => [|s x ih] z0 /=; 1: by rewrite rev_nil.
  by rewrite rev_rcons -cats1 foldr_cat -ih.
qed.

lemma foldl_cat (f : 'b -> 'a -> 'b) z0 s1 s2:
  foldl f z0 (s1 ++ s2) = foldl f (foldl f z0 s1) s2.
proof.
  by rewrite -(revK (s1 ++ s2)) foldl_rev rev_cat foldr_cat -!foldl_rev !revK.
qed.

lemma foldr_perm (f : 'a -> 'b -> 'b) (z : 'b) (s1 s2 : 'a list):
     (forall a b v, f a (f b v) = f b (f a v))
  => perm_eq s1 s2
  => foldr f z s1 = foldr f z s2.
proof.
move=> fgAC; elim: s1 s2 => [|i s1 ih] s2 eq_s12 /=.
  have ->//: s2 = [] by apply/perm_eq_small/perm_eq_sym.
have/perm_eq_mem/(_ i) := eq_s12; rewrite mem_head /=.
move/splitPr => [s3 s4] ->>; rewrite foldr_cat /=.
move: eq_s12; rewrite -(cat1s i s4) catA perm_eq_sym.
rewrite perm_catCA /= perm_cons perm_eq_sym => /ih ->.
rewrite foldr_cat; elim: s3 => [|x s3 {ih} ih] //=.
by rewrite fgAC ih.
qed.

lemma foldr_rem (x : 'a) (f : 'a -> 'b -> 'b) (z : 'b) (s : 'a list):
     (forall a b X, f a (f b X) = f b (f a X))
  => mem s x
  => foldr f z s = f x (foldr f z (rem x s)).
proof. by move=> fAC /perm_to_rem peq; rewrite (@foldr_perm f z _ _ fAC peq). qed.

(* -------------------------------------------------------------------- *)
(*                               EqIn                                   *)
(* -------------------------------------------------------------------- *)
lemma eq_in_map (f1 f2 : 'a -> 'b) (s : 'a list):
  (forall x, mem s x => f1 x = f2 x) <=> map f1 s = map f2 s.
proof. elim: s => //= x s <-; smt. qed.

lemma eq_in_filter p1 p2 (s : 'a list):
     (forall x, mem s x => p1 x <=> p2 x)
  => filter p1 s = filter p2 s.
proof.
  elim: s => //= x s ih eq_p; rewrite eq_p // ih //.
  by move=> x' x'_in_s; apply/eq_p; rewrite x'_in_s.
qed.

lemma eq_in_count (p1 p2 : 'a -> bool) (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => count p1 s = count p2 s.
proof. by move=> h; rewrite -!size_filter (eq_in_filter _ p2). qed.

lemma eq_in_has (p1 p2 : 'a -> bool) (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => has p1 s <=> has p2 s.
proof. by move=> h; rewrite !has_count (eq_in_count _ p2). qed.

lemma eq_in_all p1 p2 (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => all p1 s <=> all p2 s.
proof. by move=> h; rewrite !all_count (eq_in_count _ p2). qed.


(* -------------------------------------------------------------------- *)
(*                            Flattening                                *)
(* -------------------------------------------------------------------- *)
op flatten ['a] = foldr (++) [<:'a>].

lemma flatten_nil : flatten [<:'a list>] = [].
proof. by []. qed.

lemma flatten_cons (x : 'a list) s :
  flatten (x :: s) = x ++ flatten s.
proof. by []. qed.
    
lemma flatten_cat (s1 s2 : 'a list list):
  flatten (s1 ++ s2) = flatten s1 ++ flatten s2.
proof.
  elim: s1=> /= [|x s1 ih]; first by rewrite flatten_nil.
  by rewrite !flatten_cons ih catA.
qed.

lemma flattenP (A : 'a list list) x :
  (exists s, mem A s /\ mem s x) <=> (mem (flatten A) x).
proof.
  elim: A=> /= [|w A ih]; first by rewrite flatten_nil in_nil.
  rewrite flatten_cons mem_cat; case: (mem w x)=> /=.
    by move=> h; exists w; rewrite h.
  move=> x_notin_w; rewrite -ih; split; case=> t [].
    by case=> [->|hA] h //; exists t.
  by move=> hA h; exists t; rewrite hA.
qed.

lemma flatten_mapP (A : 'a -> 'b list) s y :
  (exists x, mem s x /\ mem (A x) y) <=> (mem (flatten (map A s)) y).
proof.
rewrite -flattenP; split; case=> [x [sx]|s' [/mapP[x [sx ->]]]] Axy.
  by exists (A x); rewrite map_f. by exists x.
qed.

op sumz (sz : int list) = foldr (+) 0 sz.

lemma size_flatten (ss : 'a list list) :
  size (flatten ss) = sumz (map size ss).
proof.
  elim: ss=> [|s ss ih] /=; first by rewrite flatten_nil.
  by rewrite flatten_cons size_cat /sumz /= ih.
qed.

lemma count_flatten (p : 'a -> bool) (ss : 'a list list) :
  count p (flatten ss) = sumz (map (count p) ss).
proof.
  elim: ss=> [|s ss ih] /=; first by rewrite flatten_nil.
  by rewrite flatten_cons count_cat /sumz /= ih.
qed.

lemma nosmt perm_undup_count (s : 'a list) :
  perm_eq
    (flatten (map (fun x => nseq (count (pred1 x) s) x) (undup s)))
    s.
proof.
move: {-1}(undup s) (perm_eq_refl (undup s))=> t.
elim: t s => [|x t ih] s eqs.
  have ->: s = []; last by apply/perm_eq_refl.
  by apply/mem_eq0=> a; rewrite -mem_undup (perm_eq_mem _ _ eqs).
pose s' := filter (predC1 x) s; have/perm_eq_uniq := eqs.
rewrite undup_uniq cons_uniq /= => [tx uqt]; have {ih} := ih s' _.
  apply/uniq_perm_eq=> //; first by apply/undup_uniq.
  move=> y; have/perm_eq_mem/(_ y) := eqs; rewrite !mem_undup /=.
  by rewrite /s' mem_filter /predC1; case: (y = x).
move/perm_cat2l/(_ (filter (pred1 x) s))/perm_eq_trans => @/s'.
move/(_ _ (perm_filterC (pred1 x) s)); rewrite filter_pred1.
rewrite flatten_cons => /perm_eqlP; rewrite perm_eq_sym=> <-.
apply/perm_cat2l/perm_eq_refl_eq; congr; apply/eq_in_map.
move=> a ta /=; case: (x = a)=> [->>//|] ne_xa.
congr; rewrite count_filter; apply/eq_count.
by move=> b; apply/eq_iff/andb_idr=> -> @/predC1; rewrite eq_sym.
qed.

(* -------------------------------------------------------------------- *)
(*                            All pairs                                 *)
(* -------------------------------------------------------------------- *)
op allpairs ['a 'b 'c] (f : 'a -> 'b -> 'c) s t =
  foldr (fun x => (++) (map (f x) t)) [] s.

lemma allpairs0l f t : allpairs<:'a, 'b, 'c> f [] t = [].
proof. by []. qed.

lemma allpairs0r f s : allpairs<:'a, 'b, 'c> f s [] = [].
proof. by elim: s. qed.

lemma allpairs_consl f x s t :
 allpairs<:'a, 'b, 'c> f (x :: s) t = map (f x) t ++ allpairs f s t.
proof. by []. qed.

lemma size_allpairs ['a 'b 'c] f s t :
  size (allpairs<:'a, 'b, 'c> f s t) = size s * size t.
proof.
elim: s => @/allpairs //= x s ih.
  by rewrite size_cat size_map ih mulzDl.
qed.

lemma allpairsP f s t z :
      (mem (allpairs<:'a, 'b, 'c> f s t) z)
  <=> (exists (p : _ * _), mem s p.`1 /\  mem t p.`2 /\ z = f p.`1 p.`2).
proof.
elim: s => @/allpairs //= x s ih; rewrite mem_cat.
case: (mem (map (f x) t) z)=> [/mapP[y [ty ->]]|] /=; 1: by exists (x, y).
move=> Nfxz; rewrite ih; split=> [|] [] [x' y'] /=.
  by case=> [sx'] [sy'] ->>; exists (x', y') => //=; rewrite sx' sy'.
case=> + [ty'] ->> -[<<-|sx']; last by exists (x', y').
by move: Nfxz; rewrite (@map_f (f x')).
qed.

lemma allpairs_uniq ['a 'b 'c] (f : 'a -> 'b -> 'c) s t :
     uniq s => uniq t
  => (forall x1 x2 y1 y2,
           mem s x1 => mem s x2 => mem t y1 => mem t y2
        => f x1 y1 = f x2 y2 => (x1 = x2 /\ y1 = y2))
  => uniq (allpairs f s t).
proof.
move=> uqs uqt inj_f; have: all (mem s) s by apply/allP.
elim: {-2}s uqs => @/allpairs //= x s1 ih [s1x' uqs1] [sx1 ss1].
rewrite cat_uniq ih //= map_inj_in_uniq ?uqt //=.
  by move=> y1 y2 ty1 ty2 eqf; have: (x = x) /\ (y1 = y2) by apply/inj_f.
apply/hasPn=> ? /allpairsP[z [s1z [] tz ->]]; apply/negP=> /mapP.
case=> y [ty Dy]; have [<<- _] //: (z.`1 = x) /\ (z.`2 = y).
by apply/inj_f=> //; move/allP/(_ z.`1 s1z): ss1.
qed.

lemma perm_eq_allpairs f s1 s2 t1 t2 :
  perm_eq s1 s2 => perm_eq t1 t2 => perm_eq
    (allpairs<:'a, 'b, 'c> f s1 t1)
    (allpairs<:'a, 'b, 'c> f s2 t2).
proof.
move=> @/allpairs eqs eqt; elim: s1 s2 eqs => [|x s1 ih] s2 /= eq_s12.
  by have ->//: s2 = [] by apply/perm_eq_small/perm_eq_sym.
have/perm_eq_mem/(_ x) := eq_s12; rewrite mem_head /=.
move/splitPr => [s3 s4] ->>; move: eq_s12.
rewrite -{1}(cat1s x s4) {1}catA perm_eq_sym perm_catCA /=.
rewrite perm_cons perm_eq_sym=> /ih /= /(perm_cat2l (map (f x) t1)).
move/perm_eq_trans; apply; elim: s3 => [|y s3 {ih} ih] /=.
  by apply/perm_cat2r/perm_eq_map.
by rewrite catA perm_catCA -catA; apply/perm_cat2l/ih.
qed.

(* -------------------------------------------------------------------- *)
(*                         Sequence sorting                             *)
(* -------------------------------------------------------------------- *)
op path (e : 'a -> 'a -> bool) (x : 'a) (p : 'a list) : bool =
  with p = []      => true
  with p = y :: p' => e x y /\ path e y p'.

op sorted (e : 'a -> 'a -> bool) (xs : 'a list) =
  with xs = []      => true
  with xs = y :: ys => path e y ys.

theory InsertSort.
  op insert (e : 'a -> 'a -> bool) (x : 'a) (s : 'a list) =
    with s = []      => [x]
    with s = y :: s' => if e x y then x :: s else y :: (insert e x s').

  op sort (e : 'a -> 'a -> bool) (s : 'a list) =
    with s = []      => []
    with s = x :: s' => insert e x (sort e s').

  lemma nosmt perm_insert (e : 'a -> 'a -> bool) x s:
    perm_eq (x :: s) (insert e x s).
  proof.
    elim s => //= y s IHs; case (e x y) => exy.
      by rewrite perm_cons perm_eq_refl.
    by rewrite perm_consCA perm_cons.
  qed.

  lemma nosmt perm_sort (e : 'a -> 'a -> bool) s: perm_eq (sort e s) s.
  proof.
    elim s=> //= x s IHs; cut h := perm_insert e x (sort e s).
    by apply perm_eqlE in h; rewrite -h perm_cons => {h}.
  qed.

  lemma nosmt sorted_insert (e : 'a -> 'a -> bool) x s:
       (forall x y, e x y \/ e y x)
    => sorted e s => sorted e (insert e x s).
  proof.
    move=> e_ltgt; case s => //= y s; case (e x y) => [-> -> // |].
    elim s x y => /= [|z s IHs] x y; first by smt.
    move=> Nexy [eyz pt_zs]; case (e x z); first by smt.
    by move=> Nexz; rewrite eyz /= IHs.
  qed.

  lemma nosmt sort_sorted (e : 'a -> 'a -> bool) (s : 'a list):
     (forall x y, e x y \/ e y x) => sorted e (sort e s).
  proof. by move=> e_ltgt; elim s => //= x s IHs; apply sorted_insert. qed.
end InsertSort.

op sort (e : 'a -> 'a -> bool) s = InsertSort.sort e s axiomatized by sortE.

lemma perm_sort e (s : 'a list): perm_eq (sort e s) s.
proof. by rewrite sortE /=; apply InsertSort.perm_sort. qed.

lemma sort_sorted (e : 'a -> 'a -> bool) s:
  (forall (x y : 'a), e x y \/ e y x) => sorted e (sort e s).
proof. by rewrite sortE /=; apply InsertSort.sort_sorted. qed.

(* -------------------------------------------------------------------- *)
(*                          Order lifting                               *)
(* -------------------------------------------------------------------- *)
op lex (e : 'a -> 'a -> bool) s1 s2 =
  with s1 = []      , s2 = []       => true
  with s1 = []      , s2 = y2 :: s2 => true
  with s1 = y1 :: s1, s2 = []       => false
  with s1 = y1 :: s1, s2 = y2 :: s2 =>
    if e y1 y2 then if e y2 y1 then lex e s1 s1 else true else false.

lemma lex_total (e : 'a -> 'a -> bool):
     (forall x y, e x y \/ e y x)
  => (forall s1 s2, lex e s1 s2 \/ lex e s2 s1).
proof. by move=> h; elim=> [|x1 s1 IHs1] [|x2 s2] //=; smt. qed.
