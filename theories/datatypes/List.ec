(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* This API has been mostly inspired from the [seq] library of the
 * ssreflect Coq extension. *)

(* -------------------------------------------------------------------- *)
require import AllCore.

(* -------------------------------------------------------------------- *)
type 'a list = [
  | "[]"
  | (::) of  'a & 'a list
].

(* -------------------------------------------------------------------- *)
op size (xs : 'a list) =
  with xs = []      => 0
  with xs = y :: ys => 1 + (size ys).

lemma size_ge0 (s : 'a list): 0 <= size s.
proof. by elim: s => //= x s; smt. qed.

local hint exact : size_ge0.

lemma size_eq0 (s : 'a list): (size s = 0) <=> (s = []).
proof. by case: s => //=; smt. qed.

lemma seq2_ind ['a 'b] (P : 'a list -> 'b list -> bool) :
  P [] [] => (forall x1 x2 s1 s2, P s1 s2 => P (x1 :: s1) (x2 :: s2)) =>
    forall s1 s2, size s1 = size s2 => P s1 s2.
proof.
move=> Pnil Pcons; elim=> [|x s ih] [|y s'] //=; 1,2:smt(size_ge0).
by move=> /addzI/ih/Pcons; apply.
qed.

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
proof. by elim: xs. qed.

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

op belast (x : 'a) s =
  with s = x' :: s' => x :: (belast x' s')
  with s = [] => [].

lemma cat0s (s : 'a list): [] ++ s = s.
proof. by []. qed.

lemma cats0 (s : 'a list): s ++ [] = s.
proof. by elim: s=> //= x s ->. qed.

lemma cat1s (x : 'a) (s : 'a list): [x] ++ s = x::s.
proof. by []. qed.

lemma cats1 (s : 'a list) (z : 'a): s ++ [z] = rcons s z.
proof. by elim: s => //= x s ->. qed.

lemma cat_cons (x : 'a) s1 s2: (x :: s1) ++ s2 = x :: (s1 ++ s2).
proof. by []. qed.

lemma catA (s1 s2 s3 : 'a list): s1 ++ (s2 ++ s3) = (s1 ++ s2) ++ s3.
proof. by elim: s1=> //= x s1 ->. qed.

lemma size_cat (s1 s2 : 'a list): size (s1 ++ s2) = size s1 + size s2.
proof. by elim: s1=> // x s1 /= ->; smt. qed.

lemma eqseq_cat (s1 s2 s3 s4 : 'a list) : size s1 = size s2 =>
  (s1 ++ s3 = s2 ++ s4) <=> (s1 = s2) /\ (s3 = s4).
proof.
elim: s1 s2 => [|x1 s1 ih] [|x2 s2] //=; rewrite ?addz_neq0 //.
by move/addzI/ih=> ->.
qed.

lemma last_cons (x y : 'a) (s : 'a list): last x (y :: s) = last y s.
proof. by []. qed.

lemma last_cat (x : 'a) (s1 s2 : 'a list):
  last x (s1 ++ s2) = last (last x s1) s2.
proof. by elim: s1 x=> //= x s1 ->. qed.

lemma last_rcons (x y : 'a) (s : 'a list): last x (rcons s y) = y.
proof. by elim: s x=> //= x s ->. qed.

lemma last_nonempty (x1 x2 : 'a) (s : 'a list):
  s <> [] =>
  last x1 s = last x2 s.
proof. by case: s. qed.

lemma size_rcons s (x : 'a):
  size (rcons s x) = (size s) + 1.
proof. by rewrite -cats1 size_cat /=. qed.

lemma cat_rcons (x : 'a) s1 s2 : rcons s1 x ++ s2 = s1 ++ x :: s2.
proof. by rewrite -cats1 -catA. qed.

lemma rcons_cat (x : 'a) s1 s2 : rcons (s1 ++ s2) x = s1 ++ rcons s2 x.
proof. by rewrite -!cats1 catA. qed.

lemma behead_cat ['a] (s1 s2 : 'a list): s1 <> [] =>
  behead (s1 ++ s2) = behead s1 ++ s2.
proof. by case: s1. qed.

lemma size_belast x s : size (belast<:'a> x s) = size s.
proof. by elim: s x => [|y s ih] x //=; rewrite ih. qed.

lemma lastI (x : 'a) s : x :: s = rcons (belast x s) (last x s).
proof. by elim: s x => [|y s ih] x //=; rewrite ih. qed.

lemma belast_cat x s1 s2 :
  belast<:'a> x (s1 ++ s2) = belast x s1 ++ belast (last x s1) s2.
proof. by elim: s1 x => [|y s1 ih] x //=; rewrite ih. qed.

lemma belast_rcons x s z : belast<:'a> x (rcons s z) = x :: s.
proof. by rewrite lastI -!cats1 belast_cat. qed.

(* -------------------------------------------------------------------- *)
(*                   rcons / induction principle                        *)
(* -------------------------------------------------------------------- *)
lemma nosmt last_ind (p : 'a list -> bool):
  p [] => (forall s x, p s => p (rcons s x)) => forall s, p s.
proof.
  move=> Hnil Hlast s; rewrite -(cat0s s).
  elim: s [] Hnil => [|x s2 IHs] s1 Hs1; first by rewrite cats0.
  by rewrite -cat_rcons (IHs (rcons s1 x)) // Hlast.
qed.

(* -------------------------------------------------------------------- *)
(*                               nseq                                   *)
(* -------------------------------------------------------------------- *)
op nseq (n : int) (x : 'a) = iter n ((::) x) [].

lemma size_nseq n (x : 'a) : size (nseq n x) = max 0 n.
proof.
elim/natind: n => [n le0n|n ge0n ih] @/nseq.
+ by rewrite iter0 //#. + by rewrite iterS //= ih /#.
qed.

lemma nseq0 (x : 'a): nseq 0 x = [].
proof. by rewrite /nseq iter0. qed.

lemma nseq0_le n (x : 'a) : n <= 0 => nseq n x = [].
proof. by move=> le0_n; rewrite /nseq iter0. qed.

lemma nseq_max0 n (x : 'a) : nseq (max 0 n) x = nseq n x.
proof.
rewrite /max; case: (0 < n) => // /lezNgt.
by rewrite nseq0 => /nseq0_le<:'a> ->.
qed.

lemma nseq1 (x : 'a) : nseq 1 x = [x].
proof. by rewrite /nseq iter1. qed.

lemma nseqS n (x : 'a) : 0 <= n => nseq (n+1) x = x :: nseq n x.
proof. by move=> le0_n; rewrite /nseq iterS. qed.

lemma nseqSr n (x : 'a): 0 <= n => nseq (n+1) x = rcons (nseq n x) x.
proof.
elim: n=> /= [|i ge0_i ih]; first by rewrite nseq0 nseq1.
by rewrite (@nseqS (i+1)) ?addz_ge0 // {1}ih nseqS.
qed.

lemma cat_nseq n1 n2 (x : 'a) : 0 <= n1 => 0 <= n2 =>
  nseq n1 x ++ nseq n2 x = nseq (n1 + n2) x.
proof.
move=> ge0_n1 ge0_n2; elim: n1 ge0_n1 => [|n1 ge0_n1 ih].
+ by rewrite nseq0.
+ by rewrite -addzAC !nseqS // 1:addz_ge0.
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
proof. by elim: xs n => //= /#. qed.

lemma onth_nth (z : 'a) xs n:
  0 <= n < size xs => onth xs n = Some (nth z xs n).
proof. by elim: xs n => //= /#. qed.

lemma nth0_head (z : 'a) xs: nth z xs 0 = head z xs.
proof. by case: xs. qed.

lemma nth_behead (z : 'a) xs n: 0 <= n =>
  nth z (behead xs) n = nth z xs (n+1).
proof. by move=> ge0_n; case: xs => //= x xs; rewrite addz1_neq0. qed.

lemma nth_default (z : 'a) s n: size s <= n => nth z s n = z.
proof.
elim: s n => //= x s ih n; case: (n = 0) => [->|_ _].
  by smt w=(size_ge0). by rewrite ih /#.
qed.

lemma nth_change_dfl ['a] (x0 x1 : 'a) xs i :
  0 <= i < size xs => nth x1 xs i = nth x0 xs i.
proof.
elim: xs i => /= [|x xs ih] i rgi; first by smt().
case: (i = 0) => //= nz_i; apply: ih => /#.
qed.

lemma nth_neg (x0 : 'a) s n: n < 0 => nth x0 s n = x0.
proof. by elim: s n => //= /#. qed.

lemma nth_out (x0 : 'a) s n: ! (0 <= n < size s) => nth x0 s n = x0.
proof.
rewrite andaE negb_and; case; rewrite (lezNgt, ltzNge) /=.
  by apply/nth_neg. by apply/nth_default.
qed.

lemma nth_cat (x0 : 'a) s1 s2 n:
  nth x0 (s1 ++ s2) n =
    if n < size s1 then nth x0 s1 n else nth x0 s2 (n - size s1).
proof.
case: (n < 0) => [n_lt0|n_ge0]; 1: smt w=(size_ge0 nth_neg).
by elim: s1 n n_ge0; smt w=(size_ge0 nth_neg).
qed.

lemma last_nth (x0 : 'a) x s : last x s = nth x0 (x :: s) (size s).
proof. by elim: s x => [|y s IHs] x //=; smt w=(size_ge0). qed.

lemma nth_last (x0 : 'a) s : nth x0 s (size s - 1) = last x0 s.
proof. by case: s => //= x s; rewrite (last_nth x0) /#. qed.

lemma nth_rcons x0 (s : 'a list) x n:
  nth x0 (rcons s x) n =
    if n < size s then nth x0 s n else if n = size s then x else x0.
proof. by elim: s n; smt w=(size_ge0 nth_neg). qed.

lemma eq_from_nth x0 (s1 s2 : 'a list):
     size s1 = size s2
  => (forall i, 0 <= i < size s1 => nth x0 s1 i = nth x0 s2 i)
  => s1 = s2.
proof.                        (* BUG: CHECKING IS TOO LONG *)
elim: s1 s2 => [|x1 s1 IHs1] [|x2 s2] //=; 1,2: smt w=(size_ge0).
move=> eq_szS h; have eq_sz: size s1 = size s2 by move=> /#.
cut := h 0 => /= ->; first smt. rewrite (IHs1 s2) // => i le_i_s1.
cut := h (i+1); smt.
qed.

lemma nth_nseq w i n (a : 'a): 0 <= i < n => nth w (nseq n a) i = a.
proof.                        (* BUG: PROOF IS TOO LONG *)
case=> ge0_i ^lt_in /ltzW le_in; have/lez_trans/(_ _ le_in) := ge0_i.
move=> {le_in} ge0_n; elim: n ge0_n i ge0_i lt_in => [|n ge0_n ih].
  by move=> i ge0_i; rewrite ltz_def eqz_leq ge0_i /= => -[].
move=> i; rewrite /nseq iterS //; elim/natcase: i.
  move=> i le0_i ge0_i; have ->//: i = 0 by rewrite eqz_leq.
move=> i ge0_i _; rewrite ltz_add2r /= => /(ih _ ge0_i).
by rewrite addz_neq0 //= -addzA /= => ->.
qed.

lemma nth_nseq_if w i n (a : 'a):
  nth w (nseq n a) i = if 0 <= i < n then a else w.
proof.
case: (0 <= i < n) => [/(@nth_nseq w)->//|le].
rewrite nth_out // size_nseq /max; case: (0 < n)=> //.
by rewrite lez_lt_asym.
qed.

lemma last_nseq (x0 x : 'a, n : int) : 0 < n => last x0 (nseq n x) = x.
proof.
move=> gt0_n; rewrite (last_nth x0) size_nseq.
rewrite (_ : max 0 n = n) 1:/# ?ltzW //=.
by rewrite eqn0Ngt ?ltzW // gt0_n /= nth_nseq /#.
qed.

lemma onth_some ['a] (xs : 'a list) (n : int) x:
  onth xs n = Some x => 0 <= n < size xs /\ nth witness xs n = x.
proof. by rewrite nth_onth => ^h -> /=; elim: xs n x h => //#. qed.

lemma onth_some_rg l n (x:'a): onth l n = Some x => 0 <= n < size l.
proof. by move/onth_some. qed.

(* -------------------------------------------------------------------- *)
(*                       Sequence membership                            *)
(* -------------------------------------------------------------------- *)
op mem (s : 'a list) (z : 'a) =
  with s = []      => false
  with s = x :: s' => (z = x) \/ mem s' z.

abbrev (\in) (z : 'a) (s : 'a list) = mem s z.

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
proof. by elim: s1 => //=; smt. qed.

lemma mem_rcons s (y : 'a):
  forall x, mem (rcons s y) x = mem (y :: s) x.
proof. by move=> x; rewrite -cats1 /= !mem_cat /= orbC. qed.

lemma mem_nth (x0 : 'a) s n : 0 <= n < size s => mem s (nth x0 s n).
proof. by elim: s n => [|x s ih] //= n; smt. qed.

lemma onth_some_mem ['a] (xs : 'a list) (n : int) x:
  onth xs n = Some x => x \in xs.
proof. by move/onth_some => [? <-]; apply/mem_nth. qed.

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
proof. by elim: s=> //= x s; smt. qed.

lemma count_size p (s : 'a list): count p s <= size s.
proof. by elim: s => //= x s; smt. qed.

op has (p : 'a -> bool) xs =
  with xs = []      => false
  with xs = y :: ys => (p y) \/ (has p ys).

op all (p : 'a -> bool) xs =
  with xs = []      => true
  with xs = y :: ys => (p y) /\ (all p ys).

lemma hasP p (s : 'a list): has p s <=> (exists x, mem s x /\ p x).
proof.
  elim: s => //= y s IHs; case: (p y) => py.
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
  elim: s=> //= x s [IH1 IH2]; split.
    by elim=> _ h y []; [move=> -> // | apply IH1].
  move=> h; split; [by apply h | apply IH2].
  by move=> y y_in_s; apply h; right.
qed.

lemma size_filter p (s : 'a list): size (filter p s) = count p s.
proof. by elim: s => //= x s; case: (p x) => _ ->. qed.

lemma filter_pred0 (s : 'a list): filter pred0 s = [].
proof. by elim: s. qed.

lemma filter_predT (s : 'a list): filter predT s = s.
proof. by elim: s => //= x s ->. qed.

lemma filter_predI (p1 p2 : 'a -> bool) (s : 'a list):
  filter (predI p1 p2) s = filter p1 (filter p2 s).
proof.
  elim: s => //= x s IHs; rewrite IHs /predI.
  by case: (p2 x) => //=; case: (p1 x) => //=.
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
proof. elim: s; smt. qed.

lemma has_nil p : has p [<:'a>] <=> false.
proof. by []. qed.

lemma has_count p (s : 'a list): has p s <=> (0 < count p s).
proof. by elim: s => //= x s -> /=; case: (p x); smt. qed.

lemma count_eq0 ['a] (p : 'a -> bool) s :
  !(has p s) <=> count p s = 0.
proof. by rewrite has_count ltzNge /= lez_eqVlt ltzNge count_ge0. qed.

lemma has_pred0 (s : 'a list): has pred0 s <=> false.
proof. by rewrite has_count count_pred0. qed.

lemma has_predT (s : 'a list): has predT s <=> (0 < size s).
proof. by rewrite has_count count_predT. qed.

lemma has_predC p (s : 'a list) : has (predC p) s = ! all p s.
proof. by elim: s => //= x s -> @/predC; case: (p x). qed.

lemma all_count p (s : 'a list): all p s <=> (count p s = size s).
proof. by elim: s => //= x s; case: (p x) => _ /=; smt. qed.

lemma all_count_in p (s : 'a list): all p s => count p s = size s.
proof. by apply/all_count. qed.

lemma all_pred0 (s : 'a list): all pred0 s <=> (size s = 0).
proof. by rewrite all_count count_pred0 eq_sym. qed.

lemma all_predT (s : 'a list): all predT s.
proof. by rewrite all_count count_predT. qed.

lemma all_predC p (s : 'a list): all (predC p) s = ! has p s.
proof. by elim: s => //= x s ->; rewrite /predC; case: (p x). qed.

lemma eq_filter p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => filter p1 s = filter p2 s.
proof. by move=> h; elim: s=> //= x l; rewrite h=> ->. qed.

lemma eq_count p1 p2 (s : 'a list):
  (forall x, p1 x <=> p2 x) => count p1 s = count p2 s.
proof. by move=> h; rewrite -!size_filter (eq_filter _ p2). qed.

lemma count_pred0_eq p (s : 'a list):
  (forall x, ! p x) => count p s = 0.
proof. by move=> eq; rewrite -(count_pred0 s) &(eq_count). qed.

lemma count_predT_eq p (s : 'a list):
  (forall x, p x) => count p s = size s.
proof. by move=> eq; rewrite -(count_predT s) &(eq_count). qed.

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
proof. by elim: s => //= x s IHs; case: (p x). qed.

lemma all_filterP p (s : 'a list): all p s <=> filter p s = s.
proof.
  split; last by move=> <-; apply filter_all.
  by elim: s => //= x s IHs [-> Hs]; rewrite IHs.
qed.

lemma filter_id p (s : 'a list): filter p (filter p s) = filter p s.
proof. by apply all_filterP; apply filter_all. qed.

lemma filter_cat p (s1 s2 : 'a list): filter p (s1 ++ s2) = filter p s1 ++ filter p s2.
proof. by elim: s1 => //= x s1 ->; case: (p x). qed.

lemma filter_cons p x (s : 'a list):
  filter p (x :: s) = if p x then x :: filter p s else filter p s.
proof. by case: (p x)=> ->. qed.

lemma filter_rcons p x (s : 'a list):
  filter p (rcons s x) = if p x then rcons (filter p s) x else filter p s.
proof. by rewrite -!cats1 filter_cat; case: (p x)=> -> /=; rewrite ?cats0. qed.

lemma count_cat p (s1 s2 : 'a list): count p (s1 ++ s2) = count p s1 + count p s2.
proof. by rewrite -!size_filter filter_cat size_cat. qed.

lemma has_cat p (s1 s2 : 'a list): has p (s1 ++ s2) <=> has p s1 \/ has p s2.
proof. by elim: s1 => //= x s1 IHs; rewrite IHs; smt. qed.

lemma all_cat p (s1 s2 : 'a list): all p (s1 ++ s2) <=> all p s1 /\ all p s2.
proof. by elim: s1 => //= x s1 IHs; rewrite IHs. qed.

lemma mem_filter (p : 'a -> bool) x s:
  mem (filter p s) x <=> p x /\ (mem s x).
proof. by elim: s => //= y s IHs; smt. qed.

lemma find_ge0 p (s : 'a list): 0 <= find p s.
proof. elim: s; smt. qed.

lemma has_find p (s : 'a list): has p s <=> (find p s < size s).
proof. elim: s; smt. qed.

lemma find_size p (s : 'a list): find p s <= size s.
proof. elim: s; smt. qed.

lemma find_cat p (s1 s2 : 'a list):
  find p (s1 ++ s2) = if has p s1 then find p s1 else size s1 + find p s2.
proof. elim: s1; smt. qed.

lemma nth_find z0 p (s : 'a list): has p s => p (nth z0 s (find p s)).
proof. elim: s; smt. qed.

lemma before_find (x0 : 'a) p s i :
  0 <= i < find p s => ! p (nth x0 s i).
proof.
elim: s i => /= [|x s ih] i; 1: by rewrite lez_lt_asym.
case: (p x)=> //= px; rewrite ?lez_lt_asym //.
rewrite lez_eqVlt eq_sym; case: (i = 0) => [<-//|_] /=.
rewrite {1 2}(_ : i = (i + -1)+1) 1:-addzA //.
by rewrite ltz_add2r ltzS => /ih.
qed.

lemma filter_pred1 x (s : 'a list) :
  filter (pred1 x) s = nseq (count (pred1 x) s) x.
proof.
elim: s=> /= @/pred1 [|y s ih]; first by rewrite nseq0.
by case: (y = x)=> //; rewrite addzC nseqS ?count_ge0.
qed.

lemma has_nseq a n (x : 'a) : has a (nseq n x) <=> (0 < n) /\ a x.
proof.
elim/natind: n => /= [n ^le0_n /lezNgt->|n ge0_n]; 1: by rewrite nseq0_le.
by rewrite nseqS //= => ->; case: (a x) => //=; rewrite ltzS.
qed.

lemma all_nseq a n (x : 'a) : all a (nseq n x) <=> n <= 0 \/ a x.
proof.
elim/natind: n => /= [n ^le0_n ->|n ge0_n]; 1: by rewrite nseq0_le.
by rewrite nseqS //= => ->; case: (a x) => //=; rewrite lezNgt ltzS ge0_n.
qed.

lemma mem_nseq n (x y: 'a): mem (nseq n x) y = (0 < n /\ x = y).
proof. by rewrite -has_pred1 has_nseq. qed.

lemma all_pred1P (x : 'a) s :
  (s = nseq (size s) x) <=> (all (pred1 x) s).
proof.
elim: s => [|y s ih] //=; first by rewrite nseq0.
by rewrite addzC nseqS //= ih.
qed.

lemma all_nthP (p : 'a -> bool) s x0 :
      (forall i, 0 <= i < size s => p (nth x0 s i))
  <=> (all p s).
proof.
elim: s => [/#|y s ih] //=; rewrite -ih; split=> [h|[h1 h2]].
  rewrite (h 0) /= 1?addzC 1?ltzS // => i [ge0_i lt_is].
  have := h (i+1); rewrite addzC ltz_add2l lt_is /=.
  by rewrite addz_ge0 // !addz_neq0 //= addzAC.
move=> i []; elim: i => [//|i ge0_i _]; rewrite addzC ltz_add2l.
by move=> lt_is; rewrite addz_neq0 //=; apply/h2.
qed.

lemma has_nthP (p : 'a -> bool) s x0 :
      (exists i, 0 <= i < size s /\ p (nth x0 s i))
  <=> (has p s).
proof.
rewrite -(eq_has (fun x => ! (!p x))) // has_predC.
by rewrite -(all_nthP _ _ x0) /= /#.
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

lemma nosmt onth_index ['a] (x : 'a) xs:
  x \in xs => onth xs (index x xs) = Some x.
proof.
move=> x_in_xs; rewrite (onth_nth witness).
+ by rewrite index_mem index_ge0. + by rewrite nth_index.
qed.

lemma nosmt onth_mem ['a] (x : 'a) xs:
  x \in xs => exists n, onth xs n = Some x.
proof. by move/onth_index=> <-; exists (index x xs). qed.

lemma index_cat x (s1 s2 : 'a list):
 index x (s1 ++ s2) = if mem s1 x then index x s1 else size s1 + index x s2.
proof. by rewrite /index find_cat has_pred1. qed.

lemma index_head x (s : 'a list): index x (x :: s) = 0.
proof. by []. qed.

lemma before_index (x0 : 'a) x s i :
  0 <= i < index x s => nth x0 s i <> x.
proof. by move/(@before_find x0). qed.

(* -------------------------------------------------------------------- *)
(*                            drop, take                                *)
(* -------------------------------------------------------------------- *)
op drop n (xs : 'a list) =
  with xs = []      => []
  with xs = y :: ys =>
    if n <= 0 then xs else drop (n-1) ys.

lemma drop0 (s : 'a list): drop 0 s = s.
proof. by elim: s. qed.

lemma drop_le0 n (s : 'a list): n <= 0 => drop n s = s.
proof. by elim: s=> //= x s _ -> /=. qed.

lemma drop_oversize n (s : 'a list):
  size s <= n => drop n s = [].
proof. by elim: s n => /#. qed.

lemma drop_size (s : 'a list): drop (size s) s = [].
proof. by rewrite drop_oversize. qed.

lemma drop_cons n x (s : 'a list):
  drop n (x :: s) = if 0 < n then drop (n-1) s else x :: s.
proof. by rewrite /= lezNgt; case: (0 < n). qed.

lemma size_drop n (s : 'a list):
  0 <= n => size (drop n s) = max 0 (size s - n).
proof. by elim: s n => //= /#. qed.

lemma drop_cat n (s1 s2 : 'a list):
  drop n (s1 ++ s2) =
    if n < size s1 then drop n s1 ++ s2 else drop (n - size s1) s2.
proof. by elim: s1 n => /= [|x s ih] n; smt ml=0 w=(drop_le0 size_ge0). qed.

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
proof. by elim: s. qed.

lemma take_le0 n (s : 'a list): n <= 0 => take n s = [].
proof. by elim: s => //= x s _ ->. qed.

lemma take_oversize n (s : 'a list):
  size s <= n => take n s = s.
proof. by elim: s n => //= /#. qed.

lemma take_size (s : 'a list): take (size s) s = s.
proof. by rewrite take_oversize. qed.

lemma take_cons n x (s : 'a list):
  take n (x :: s) = if 0 < n then x :: take (n-1) s else [].
proof. by rewrite /= lezNgt; case: (0 < n). qed.

lemma size_take n (s : 'a list):
  0 <= n => size (take n s) = if n < size s then n else size s.
proof. by elim: s n => //= /#. qed.

lemma size_takel n (s : 'a list ):
  0 <= n <= size s => size (take n s) = n.
proof.
case=> ge0_n le_sz; rewrite size_take //; move: le_sz.
by rewrite lez_eqVlt => -[] ->.
qed.

lemma size_take_le n (s : 'a list) : 0 <= n => size (take n s) <= n.
proof.
move=> ge0_n; case: (n <= size s).
+ by move=> gt_ns; rewrite size_takel // ge0_n.
+ by move=> /ltzNge lt_sn; rewrite take_oversize 1?ltzW.
qed.

lemma take_cat n (s1 s2 : 'a list):
   take n (s1 ++ s2) =
     if n < size s1 then take n s1 else s1 ++ take (n - size s1) s2.
proof. by elim: s1 n => //=; smt ml=0 w=(take_le0 size_ge0). qed.

lemma take_size_cat n (s1 s2 : 'a list):
  size s1 = n => take n (s1 ++ s2) = s1.
proof. by move=> <-; rewrite take_cat subzz ltzz take0 cats0. qed.

lemma take_nth (z0 : 'a) n s: 0 <= n < size s =>
  take (n+1) s = rcons (take n s) (nth z0 s n).
proof.
elim: s n=> [|x s ih] n []; 1: by elim: n => [|n _] hn //=; 1: smt.
by elim: n => [|n ge0_n _] /=; rewrite ?take0 //= /#.
qed.

lemma cat_take_drop n (s : 'a list): take n s ++ drop n s = s.
proof. by elim: s n=>/#. qed.

lemma mem_drop n (s:'a list) x: mem (drop n s) x => mem s x.
proof. by rewrite -{2}(cat_take_drop n) mem_cat=>->. qed.

lemma mem_take n (s:'a list) x: mem (take n s) x => mem s x.
proof. by rewrite -{2}(cat_take_drop n) mem_cat=>->. qed.

lemma nth_drop (x0 : 'a) n s i:
  0 <= n => 0 <= i => nth x0 (drop n s) i = nth x0 s (n + i).
proof.
  move=> n_ge0 i_ge0; case: (n < size s) => [lt_n_s|le_s_n]; last smt.
  rewrite -{2}(cat_take_drop n s) nth_cat size_take //; smt.
qed.

lemma nth_take (x0 : 'a) n s i:
  0 <= n => i < n => nth x0 (take n s) i = nth x0 s i.
proof.
  move=> n_ge0 i_ge0; case: (n < size s) => [lt_n_s|le_s_n]; last smt.
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

lemma rot_le0 n (s : 'a list): n <= 0 => rot n s = s.
proof. by move=> le0_n; rewrite /rot !(drop_le0, take_le0) // cats0. qed.

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
  elim: s s_x => //= y s IHs; case: (x = y); smt.
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
  move=> i i_ge0 IHi a le_ai; case: (count a (s1 ++ s2) = 0).
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

lemma  perm_eqrE ['a]:
  forall (s1 s2 : 'a list),
    perm_eq s1 s2 => forall (s : 'a list), perm_eq s s1 <=> perm_eq s s2.
proof.
by move=> s1 s2 h s; rewrite !(perm_eq_sym s); move/perm_eqlE: h=> ->.
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
  case: s2 => [|x []] //=; first last; last 2 smt.
  case: s1 => [|y []] //=; last smt.
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
  elim: s => //= y s IHs; rewrite negb_or; elim.
  move=> neq_yz s_notin_z; rewrite IHs // (eq_sym y).
  by cut ->: (z = y) <=> false.
qed.

lemma perm_to_rem (z : 'a) s : mem s z => perm_eq s (z :: rem z s).
proof.
  elim: s => //= y s IHs; rewrite eq_sym perm_eq_sym.
  rewrite -oraE; elim; first by move=> -> /=; rewrite perm_eq_refl.
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

lemma count_rem ['a] (p : 'a -> bool) (s : 'a list) x : x \in s =>
  count p s = b2i (p x) + count p (rem x s).
proof. by move/perm_to_rem/perm_eqP/(_ p)=> ->. qed.

lemma count_gt0 ['a] (p : 'a -> bool) s :
  0 < count p s => exists x,
    perm_eq s (x :: rem x s) /\ p x /\ count p (rem x s) = count p s - 1.
proof.
rewrite -has_count => /hasP[x [x_in_s px]]; exists x; do! split => //.
+ by apply/perm_to_rem.
+ by move/perm_eqP: (perm_to_rem _ _ x_in_s) => -> /#.
qed.

lemma count_eq1 ['a] (p : 'a -> bool) s :
  count p s = 1 => exists x,
    x \in s /\ p x /\ forall y, y \in s => y <> x => !p y.
proof.
move=> h; have /count_gt0 [c] |>: 0 < count p s by smt().
move=> eqs pc hc; exists c; do! split=> //.
+ by move/perm_eq_mem: eqs => ->.
move=> c' c'_in_s ne; move: hc; rewrite h /=.
move/count_eq0; apply contra => pc'; apply/hasP.
exists c'; rewrite pc' /=; have: c' \in c :: rem c s.
+ by move/perm_eq_mem: eqs => <-.
+ by rewrite /= ne.
qed.

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
proof.
move=> [] le0_n ltn_size; rewrite size_cat size_take ?ltn_size //=.
by rewrite size_drop /#.
qed.

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
proof.
rewrite size_cat /trim take_cat drop_cat.
case: (n + 1 < size xs)=> [lt_n1_sx|/lezNgt].
  have ->: (n < size xs) by smt. (* n + 1 < size xs => n < size xs *)
  by rewrite catA.
case: (n < size xs)=> /=; last first.
  by rewrite catA addzAC.
rewrite -lez_add1r addzC=> h h'.
have {h h'} sx_eq_n1:= lez_anti (size xs) (n + 1) _=> //.
rewrite sx_eq_n1 Ring.IntID.opprD.
rewrite (addzC (-n)) addzA -(addzA _ _ (-1)) /=.
by rewrite drop0 -sx_eq_n1 drop_size cats0.
qed.

(* -------------------------------------------------------------------- *)
(*                        Sequence reversal                             *)
(* -------------------------------------------------------------------- *)
op catrev (s1 s2 : 'a list) =
  with s1 = []      => s2
  with s1 = x :: s1 => catrev s1 (x :: s2).

op rev (s : 'a list) = catrev s [].

lemma catrev_catl (s t u : 'a list):
  catrev (s ++ t) u = catrev t (catrev s u).
proof. by elim: s u => //= x s h u; rewrite h. qed.

lemma catrev_catr (s t u : 'a list):
  catrev s (t ++ u) = catrev s t ++ u.
proof. by elim: s t => //= x s IHs t; rewrite -IHs. qed.

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
  elim: s; first by rewrite /rev.
  by move=> x s IHs; rewrite rev_cons size_rcons IHs /=; smt.
qed.

lemma rev_cat (s t : 'a list): rev (s ++ t) = rev t ++ rev s.
proof. by rewrite /rev -catrev_catr /= -catrev_catl. qed.

lemma rev_rcons s (x : 'a): rev (rcons s x) = x :: rev s.
proof. by rewrite -cats1 rev_cat /rev /=. qed.

lemma last_rev ['a] (x0 : 'a) (s : 'a list) :
  last x0 (rev s) = head x0 s.
proof. by case: s => [|x s]; rewrite ?rev_nil ?rev_cons ?last_rcons. qed.

lemma revK (s : 'a list): rev (rev s) = s.
proof. by elim: s; smt. qed.

lemma rev_inj : injective rev<:'a>.
proof. by move=> s1 s2 /(congr1 rev); rewrite !revK. qed.

lemma catsI (s t1 t2 : 'a list): s ++ t1 = s ++ t2 => t1 = t2.
proof. by move=> h; have /eqseq_cat /= <-: size s = size s by done. qed.

lemma catIs (s1 s2 t : 'a list): s1 ++ t = s2 ++ t => s1 = s2.
proof. by move/(congr1 rev); rewrite !rev_cat => /catsI /rev_inj. qed.

lemma rconsIs ['a] xs xs' (x x' : 'a):
  rcons xs x = rcons xs' x' => x = x'.
proof. by move=> /(congr1 (last witness)); rewrite !last_rcons. qed.

lemma rconssI ['a] (x x' : 'a) xs xs':
  rcons xs x = rcons xs' x' => xs = xs'.
proof. by move=> ^ /rconsIs ->>; rewrite -!cats1=> /catIs. qed.

lemma mem_rev (s : 'a list):
  forall x, mem (rev s) x = mem s x.
proof.
  move=> x; elim: s; first by rewrite rev_nil.
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

lemma rev_nseq n (x : 'a): rev (nseq n x) = nseq n x.
proof.
elim/natind: n => [n /nseq0_le<:'a> ->//|n ge0_n].
by rewrite {1}nseqS ?nseqSr // rev_cons => ->.
qed.

lemma nth_rev (x0 : 'a) n s :
  0 <= n < size s => nth x0 (rev s) n = nth x0 s (size s - (n+1)).
proof.
elim/last_ind: s n=> /= [|x s ih] n; first by rewrite lez_lt_asym.
rewrite rev_rcons size_rcons ltzS subz_add2r -cats1 nth_cat /=.
elim/natcase: n=> [n le0_n|n ge0_n] [ge0_Hn lt_ns] /=.
  by have ->: n = 0 by rewrite eqz_leq le0_n ge0_Hn.
rewrite addz_neq0 //= -{2}(addz0 (size x)).
by rewrite ltz_add2l oppz_lt0 ltzS ge0_n /= -ih ?ltzE ?ge0_n // -addzA.
qed.

lemma perm_eq_rev (s : 'a list) : perm_eq s (rev s).
proof. by rewrite perm_eqP=> p; rewrite count_rev. qed.

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
  elim: s1 => [|x s1 IHs]; first by rewrite /= in_nilE has_pred0.
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
proof. by elim: s => //=; smt. qed.

lemma rot_uniq n (s : 'a list): uniq (rot n s) = uniq s.
proof. by rewrite /rot uniq_catC cat_take_drop. qed.

lemma rev_uniq (s : 'a list): uniq (rev s) <=> uniq s.
proof.
  elim: s => /=; [by rewrite rev_nil | move=> x s IHs].
  by rewrite rev_cons -cats1 cat_uniq IHs /= mem_rev.
qed.

lemma rem_filter x (s : 'a list): uniq s =>
  rem x s = filter (predC1 x) s.
proof.
  elim: s => //= y s ih [y_notin_s /ih->]; rewrite /predC1.
  case: (y = x)=> //= <-; apply/eq_sym/all_filterP.
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
proof. by elim: s => //= x s IHs; smt. qed.

lemma mem_undup (s : 'a list): forall x, mem (undup s) x = mem s x.
proof. move=> x; elim: s => //= y s IHs; smt. qed.

lemma undup_uniq (s : 'a list): uniq (undup s).
proof. by elim: s => //= x s IHs; case: (mem s x); smt. qed.

lemma undup_id (s : 'a list): uniq s => undup s = s.
proof. by elim: s => //= x s IHs; smt. qed.

lemma count_uniq_mem s (x : 'a):
  uniq s => count (pred1 x) s = b2i (mem s x).
proof. elim: s; smt. qed.

lemma uniq_leq_size (s1 s2 : 'a list):
  uniq s1 => (mem s1 <= mem s2) => size s1 <= size s2.
proof.                          (* FIXME: test case: for views *)
  rewrite /Core.(<=); elim: s1 s2 => //.
  move=> x s1 IHs s2 [not_s1x Us1]; rewrite -(allP (mem s2)) /=.
  case=> s2x; rewrite allP => ss12; cut := rot_to s2 x _ => //.
  case=> i s3 def_s2; rewrite -(size_rot i s2) def_s2 /= lez_add2l.
  apply IHs => // y s1y; cut := ss12 y _ => //.
  by rewrite -(mem_rot i) def_s2; case.
qed.

lemma leq_size_uniq (s1 s2 : 'a list):
  uniq s1 => (mem s1 <= mem s2) => size s2 <= size s1 => uniq s2.
proof.
  rewrite /Core.(<=); elim: s1 s2 => [[] | x s1 IHs s2] //; first smt.
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
  rewrite -andaE; split=> [|h]; last by rewrite eq_sym -uniq_size_uniq.
  move=> x; split; [by apply ss12 | move=> s2x; move: le_s21].
  apply absurd => not_s1x; rewrite -ltzNge -lez_add1r.
  cut := uniq_leq_size (x :: s1) => /= -> //=.
  by rewrite /Core.(<=) -(allP (mem s2)) /= s2x /= allP.
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

lemma undup_nilp (s : 'a list) : (undup s = []) <=> (s = []).
proof.
split=> [|->] // /(congr1 mem) h; rewrite mem_eq0 // => x.
by rewrite -mem_undup h.
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
  by apply/negP => /(map_f f).
qed.

lemma map_cons (f : 'a -> 'b) x s: map f (x :: s) = f x :: map f s.
proof. by []. qed.

lemma map_cat (f : 'a -> 'b) s1 s2:
  map f (s1 ++ s2) = map f s1 ++ map f s2.
proof. by elim: s1 => [|x s1 IHs] //=; rewrite IHs. qed.

lemma size_map (f : 'a -> 'b) s: size (map f s) = size s.
proof. by elim: s => [// | x s /= ->]. qed.

lemma map_comp (f1 : 'b -> 'c) (f2 : 'a -> 'b) s:
  map (f1 \o f2) s = map f1 (map f2 s).
proof. by elim: s => //= x s ->. qed.

lemma map_id (s : 'a list): map idfun s = s.
proof. by elim: s => //= x s ->. qed.

lemma id_map f (s : 'a list): (forall x, f x = x) => map f s = s.
proof. by move=> h; rewrite -{2}(@map_id s); apply/eq_map. qed.

lemma nth_map x1 x2 (f : 'a -> 'b) n s:
  0 <= n < size s => nth x2 (map f s) n = f (nth x1 s n).
proof. by elim: s n; smt. qed.

lemma onth_nth_map (s : 'a list) n: onth s n = nth None (map Some s) n.
proof. by elim: s n; smt. qed.

lemma map_rcons (f : 'a -> 'b) s x:
  map f (rcons s x) = rcons (map f s) (f x).
proof. by rewrite -!cats1 map_cat. qed.

lemma last_map (f : 'a -> 'b) s x:
  last (f x) (map f s) = f (last x s).
proof. by elim: s x => //= x s ->. qed.

lemma filter_map (f : 'a -> 'b) p s:
  filter p (map f s) = map f (filter (preim f p) s).
proof.
  by elim: s => //= x s IHs; rewrite (fun_if (map f)) /= IHs.
qed.

lemma has_map (f : 'a -> 'b) p s:
  has p (map f s) = has (preim f p) s.
proof. by elim: s => //= x s ->. qed.

lemma all_map (f :  'a -> 'b) p s:
  all p (map f s) = all (preim f p) s.
proof. by elim: s => //= x s ->. qed.

lemma count_map (f : 'a -> 'b) p s:
  count p (map f s) = count (preim f p) s.
proof. by elim: s => //= x s ->. qed.

lemma map_take (f : 'a -> 'b) n s:
  map f (take n s) = take n (map f s).
proof.
  elim: s n => //= x s IHs n.
  by case: (n <= 0) => // _; rewrite IHs.
qed.

lemma map_drop (f : 'a -> 'b) n s:
  map f (drop n s) = drop n (map f s).
proof.
  elim: s n => //= x s IHs n.
  by case: (n <= 0) => // _; rewrite IHs.
qed.

lemma map_rev (f : 'a -> 'b) s:
  map f (rev s) = rev (map f s).
proof. elim: s; first by rewrite rev_nil. smt. qed.

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
  rewrite addz1_neq0 1:index_ge0 //= ih //.
  by move=> x' y' s_x' s_y'; apply/inj_f; rewrite ?(s_x', s_y').
qed.

lemma in_inj_map ['a 'b] (f : 'a -> 'b) p :
     (forall x y, p x => p y => f x = f y => x = y)
  => forall s1 s2, all p s1 => all p s2 => map f s1 = map f s2 => s1 = s2.
proof.
move=> inj_f; elim=> [|x1 s1 ih] [|x2 s2] //=.
case=> [p1 ps1] [p2 ps2] [eqf eqm].
by rewrite (inj_f x1 x2) //=; apply/ih.
qed.

lemma inj_map ['a 'b] (f : 'a -> 'b) :
  injective f => injective (map f).
proof.
by move=> inj_f s1 s2; apply/(@in_inj_map _ predT); try apply/all_predT.
qed.

lemma nosmt onth_map_some ['a 'b] (f : 'a->'b) (xs : 'a list) n v:
 onth (map f xs) n = Some v <=> exists y, onth xs n = Some y /\ v = f y.
proof.
by elim: xs n => //= x xs ih n; case: (n = 0) => _; [smt() | apply/ih].
qed.

lemma index_map ['a 'b] (f : 'a -> 'b) x xs:
 injective f => index (f x) (map f xs) = index x xs.
proof.
move=> /inj_eq inj_f; elim: xs => // x' xs ih.
rewrite map_cons !index_cons inj_f; case: (x = x') => //.
by move=> _; rewrite ih.
qed.

(* -------------------------------------------------------------------- *)
(*                         Partial mapping                              *)
(* -------------------------------------------------------------------- *)
op pmap ['a 'b] (f : 'a -> 'b option) (s : 'a list) =
  with s = []     => []
  with s = x :: s =>
    if f x = None then pmap f s else oget (f x) :: pmap f s.

lemma map_pK ['a 'b] (f : 'a -> 'b option) g :
  pcancel g f => cancel (map g) (pmap f).
proof. by move=> gK; elim=> //= x s ->; rewrite gK. qed.

lemma pmap_map ['a 'b] (f : 'a -> 'b option) s:
  pmap f s = map oget (filter (predC1 None) (map f s)).
proof. by elim: s => //= x s ih; case: (f x) => @/predC1. qed.

lemma pmap_cat ['a 'b] (f : 'a -> 'b option) s1 s2:
  pmap f (s1 ++ s2) = pmap f s1 ++ pmap f s2.
proof. by rewrite !pmap_map !(map_cat, filter_cat). qed.

lemma pmap_none ['a 'b] s : pmap (fun (i : 'a) => None<:'b>) s = [].
proof. by elim: s. qed.

lemma pmap_some ['a 'b] (f : 'a -> 'b) s:
  pmap (fun x => Some (f x)) s = map f s.
proof.
rewrite pmap_map filter_map -!map_comp.
by rewrite -(@eq_filter predT) ?filter_predT.
qed.

lemma pmap_inj_in_uniq (f : 'a -> 'b option) (s : 'a list) :
      (forall (x y : 'a) v, x \in s => y \in s =>
         f x = Some v => f y = Some v => x = y)
   => uniq s => uniq (pmap f s).
proof.
elim: s => //= x s ih inj_f [xs uqs]; case _: (f x) => /= [|v] E.
- by rewrite ih // => x' y' v' x's y's; apply/inj_f; right.
rewrite ih //; 1: by move => x' y' v' x's y's; apply/inj_f; right.
rewrite /oget /= pmap_map; apply/negP => /mapP.
case=> -[|v']; rewrite mem_filter // => -[[_ vs] @/oget /=].
apply/negP=> <<-; move: vs; rewrite -E => /mapP.
case=> y [ys eq_f]; suff <<-//: x = y.
by apply: (@inj_f x y v); rewrite ?ys //= -eq_f.
qed.

lemma pmapP ['a, 'b] (f : 'a -> 'b option) s y :
  y \in pmap f s <=> exists (x : 'a), (x \in s) /\ Some y = f x.
proof.
rewrite pmap_map; split => [|/mapP].
+ case/mapP=> z; rewrite mem_filter /predC1 => />.
  by case: z => // z _ /mapP; apply.
+ case/mapP=> x [xs fxE]; apply/mapP; exists (Some y).
  by rewrite mem_filter /predC1 /=; apply/mapP; exists x.
qed.

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
    + by rewrite iota0 //#. + by rewrite iotaS //= ih //#.
  qed.

  lemma iota_add m n1 n2 : 0 <= n1 => 0 <= n2 =>
     iota_ m (n1 + n2) = iota_ m n1 ++ iota_ (m + n1) n2.
  proof.
    move=> ge0_n1 ge0_n2; elim: n1 ge0_n1 m => /= [|n1 ge0_n1 ih] m.
      by rewrite (iota0 m 0).
    by rewrite addzAC !iotaS // 1:smt ih addzAC addzA.
  qed.

  lemma iotaSr i n : 0 <= n =>
    iota_ i (n+1) = rcons (iota_ i n) (i+n).
  proof. by move=> ge0_n; rewrite iota_add // iota1 cats1. qed.

  lemma nth_iota m n i w: 0 <= i < n => nth w (iota_ m n) i = m + i.
  proof.
    case=> ge0_i lt_in; rewrite (_ : n = i + ((n-i-1)+1)) 1:/#.
    rewrite iota_add // 1:/# nth_cat size_iota (_ : max 0 i = i) 1:/#.
    by rewrite /= (iotaS _ (n-i-1)) //#.
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

  lemma mema_iota m n i : mem (iota_ m n) i <=> (m <= i < m + n).
  proof. by rewrite mem_iota andaE. qed.

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

  lemma take_iota (k n m : int):
    take k (iota_ n m) = iota_ n (min m k).
  proof.
  move=> @/min; case: (m < k)=> [lt_mk|/lezNgt le_km].
    case: (m < 0) => [/ltzW/iota0->//|/lezNgt ge0_m].
    by rewrite take_oversize // size_iota /#.
  case: (k < 0) => [^ /ltzW /take_le0<:int> -> /ltzW/iota0 ->//|].
  move/lezNgt=> ge0_k; rewrite -{1}(addzK (-k) m) /=.
  rewrite addzC iota_add ?subz_ge0 // take_cat.
  by rewrite size_iota (_ : max 0 k = k) 1:/# // ltzz /= take0 cats0.
  qed.

  lemma drop_iota (k n m : int): 0 <= k =>
    drop k (iota_ n m) = iota_ (n+k) (m-k).
  proof.
  move=> ge0_k; case: (m < k) => [lt_mk|/lezNgt le_km].
    rewrite drop_oversize ?size_iota 1:/# ?(@ltzW m) //.
    by rewrite iota0 // subz_le0 ltzW.
  rewrite -{1}(addzK (-k) m) /= addzC.
  rewrite iota_add ?subz_ge0 // drop_cat size_iota.
  by rewrite (_ : max 0 k = k) 1:/# // ltzz /= drop0.
  qed.

  lemma nosmt onth_iota_some start sz n x:
    onth (iota_ start sz) n = Some x <=> 0 <= n < sz /\ x = start + n.
  proof. split.
  + by move/onth_some; rewrite size_iota => -[h]; rewrite nth_iota /#.
  + move=> h; rewrite (onth_nth witness) 1:size_iota 1:/#.
    by congr; rewrite nth_iota /#.
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
  proof. by rewrite -{1}(addrNK a n) range_add. qed.

  lemma range_addr (m n a : int):
    range m (n+a) = map (Int.(+) a) (range (m-a) n).
  proof. by rewrite -{1}(addrNK a m) range_add. qed.

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
    by rewrite addrCA addrN addr0.
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
lemma map_nth_range (x0 : 'a) s:
  map (fun i => nth x0 s i) (range 0 (size s)) = s.
proof.
apply/(@eq_from_nth x0)=> [|i]; rewrite ?size_map.
  by rewrite size_range /=; smt(size_ge0).
move=> le_is; rewrite (@nth_map i) //= nth_range //=.
by move: le_is; rewrite size_range; smt(size_ge0).
qed.

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
  rewrite /assoc /= index_cons /=; case: (a = x)=> //=.
  by move=> _; rewrite addz1_neq0 // index_ge0.
qed.

lemma assoc_head x y s: assoc<:'a, 'b> ((x, y) :: s) x = Some y.
proof. by rewrite assoc_cons. qed.

lemma assoc_cat (s1 s2 : ('a * 'b) list) x:
    assoc (s1 ++ s2) x
  = if mem (map fst s1) x then assoc s1 x else assoc s2 x.
proof.
  elim: s1 => /= [|[x' y'] s ih] //; rewrite !assoc_cons /=.
  by case: (x = x').
qed.

lemma mem_assoc_uniq (s : ('a * 'b) list) (a : 'a) (b : 'b):
  uniq (map fst s) => mem s (a, b) <=> assoc s a = Some b.
proof.
  elim: s => //= [[x y]] s ih; rewrite eq_sym => -[x_notin_1s uq_1s] /=.
  case: (x = a) => [->> |] /=; 1: rewrite assoc_head /=.
    by apply/orb_idr=> /(map_f fst); rewrite x_notin_1s.
  by move=> ne_xa; rewrite assoc_cons ih // (@eq_sym a) ne_xa.
qed.

lemma assocP (s : ('a * 'b) list) (x : 'a):
     (  mem (map fst s) x /\ exists y, mem s (x, y) /\ assoc s x = Some y)
  \/ (! mem (map fst s) x /\ assoc s x = None).
proof.
  elim: s=> //=; case=> x' y' s ih /=.
  case: (x = x') => /= [<<- |]; 1: by exists y'; rewrite assoc_cons.
  by rewrite assoc_cons => ->.
qed.

lemma nosmt assocTP ['a 'b] (xs : ('a * 'b) list) k :
  assoc xs k <> None <=> k \in map fst xs.
proof.
by split=> h; have := assocP xs k; rewrite h //= => -[b [_ ->]].
qed.

lemma assoc_some ['a, 'b] (xs : ('a * 'b) list) k v:
 assoc xs k = Some v => (k, v) \in xs.
proof.
by elim: xs => // -[a b] xs ih /=; rewrite assoc_cons; case: (k = a).
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
    rewrite {1}/(\o) /=; case: (p x).
    by rewrite assoc_cons. by rewrite ih=> ->.
  by case: ((\o) _ _ _)=> //=; rewrite assoc_cons ne_xx'.
qed.

lemma assoc_get_mem ['a 'b] (xs : ('a * 'b) list) k:
  k \in map fst xs => (k, oget (assoc xs k)) \in xs.
proof.
elim: xs => // [[k' v] xs] ih /= [<<- /=|]; 1: by rewrite assoc_cons.
by rewrite !assoc_cons /= => /ih {ih}ih; case: (k = k').
qed.

lemma nosmt assoc_some_onth_mem ['a 'b] (xs : ('a * 'b) list) (k : 'a) (v : 'b):
 assoc xs k = Some v => (exists n, onth xs n = Some (k, v)).
proof. by move/assoc_some => /onth_mem. qed.

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
by move=> lt_in; rewrite /mkseq (nth_map 0) ?nth_iota ?size_iota /#.
qed.

lemma nth_mkseq_if x0 (f : int -> 'a) n i:
  nth x0 (mkseq f n) i = if 0 <= i < n then f i else x0.
proof.
case: (0 <= i < n)=> [/(nth_mkseq x0) ->//|h]; rewrite nth_out //.
rewrite size_mkseq /max; case: (0 < n)=> // _; smt ml=0.
qed.

lemma mkseq_nth (x0 : 'a) s: mkseq (nth x0 s) (size s) = s.
proof.
  apply (eq_from_nth x0); rewrite size_mkseq; first smt.
  by move=> i Hi; rewrite nth_mkseq //; smt.
qed.

lemma mkseq0 (f : int -> 'a) : mkseq f 0 = [].
proof. by rewrite /mkseq iota0. qed.

lemma mkseq0_le f n : n <= 0 => mkseq<:'a> f n = [].
proof. by move=> ge0_n @/mkseq; rewrite iota0. qed.

lemma mkseq1 f : mkseq<:'a> f 1 = [f 0].
proof. by rewrite /mkseq iota1. qed.

lemma mkseqS f n : 0 <= n =>
  mkseq<:'a> f (n + 1) = rcons (mkseq f n) (f n).
proof. by move=> ge0_n; rewrite /mkseq iotaSr //= map_rcons. qed.

lemma mkseq_add (f : int -> 'a) n m : 0 <= n => 0 <= m =>
  mkseq f (n+m) = mkseq f n ++ mkseq (fun i => f (n+i)) m.
proof.
move=> ge0_n ge0_m; rewrite /mkseq iota_add ?map_cat //=.
by rewrite -{2}(addz0 n) iota_addl -map_comp.
qed.

lemma mkseqP f n (x:'a) :
  mem (mkseq f n) x <=> exists i, 0 <= i < n /\ x = f i.
proof. by rewrite mapP &(exists_iff) /= => i; rewrite mem_iota. qed.

(* -------------------------------------------------------------------- *)
(*                         Sequence folding                             *)
(* -------------------------------------------------------------------- *)
op foldr (f : 'a -> 'b -> 'b) z0 xs =
  with xs = []      => z0
  with xs = y :: ys => f y (foldr f z0 ys).

lemma foldr_cat (f : 'a -> 'b -> 'b) z0 s1 s2:
  foldr f z0 (s1 ++ s2) = foldr f (foldr f z0 s2) s1.
proof. by elim: s1 => //= x s1 ->. qed.

lemma foldr_map ['a 'b 'c] (f : 'a -> 'b -> 'b) (h : 'c -> 'a) z0 s:
  foldr f z0 (map h s) = foldr (fun x z, f (h x) z) z0 s.
proof. by elim: s => //= x s ->. qed.

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

lemma eq_in_pmap ['a 'b] (f1 f2 : 'a -> 'b option) s:
     (forall x, mem s x => f1 x = f2 x)
  => pmap f1 s = pmap f2 s.
proof. by move=> eq; rewrite !pmap_map; do 2!congr; apply/eq_in_map. qed.

lemma eq_in_filter p1 p2 (s : 'a list):
     (forall x, mem s x => p1 x <=> p2 x)
  => filter p1 s = filter p2 s.
proof.
  elim: s => //= x s ih eq_p; rewrite eq_p // ih //.
  by move=> x' x'_in_s; apply/eq_p; rewrite x'_in_s.
qed.

lemma eq_in_filter_predT (P : 'a -> bool) s:
  (forall x, mem s x => P x) => filter P s = s.
proof. by move=> Ps; rewrite (@eq_in_filter P predT) ?filter_predT. qed.

lemma eq_in_filter_pred0 (P : 'a -> bool) s:
  (forall x, mem s x => !P x) => filter P s = [].
proof. by move=> Ps; rewrite (@eq_in_filter P pred0) ?filter_pred0. qed.

lemma eq_in_count (p1 p2 : 'a -> bool) (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => count p1 s = count p2 s.
proof. by move=> h; rewrite -!size_filter (eq_in_filter _ p2). qed.

lemma eq_in_has (p1 p2 : 'a -> bool) (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => has p1 s <=> has p2 s.
proof. by move=> h; rewrite !has_count (eq_in_count _ p2). qed.

lemma eq_in_all p1 p2 (s : 'a list):
  (forall x, mem s x => p1 x <=> p2 x) => all p1 s <=> all p2 s.
proof. by move=> h; rewrite !all_count (eq_in_count _ p2). qed.

lemma eq_in_mkseq (f1 f2 : int -> 'a) n:
     (forall i, 0 <= i < n => f1 i = f2 i)
  => mkseq f1 n = mkseq f2 n.
proof. by move=> h; rewrite -eq_in_map=> x /mema_iota /h. qed.

(* -------------------------------------------------------------------- *)
(*                            Flattening                                *)
(* -------------------------------------------------------------------- *)
op flatten ['a] = foldr (++) [<:'a>].

lemma flatten_nil : flatten [<:'a list>] = [].
proof. by []. qed.

lemma flatten_cons (x : 'a list) s :
  flatten (x :: s) = x ++ flatten s.
proof. by []. qed.

lemma flatten_seq1 (s : 'a list) : flatten [s] = s.
proof. by rewrite flatten_cons flatten_nil cats0. qed.

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

op sumz (sz : int list) = foldr Int.(+) 0 sz.

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
rewrite undup_uniq cons_uniq /= => -[tx uqt]; have {ih} := ih s' _.
  apply/uniq_perm_eq=> //; first by apply/undup_uniq.
  move=> y; have/perm_eq_mem/(_ y) := eqs; rewrite !mem_undup /=.
  by rewrite /s' mem_filter /predC1; case: (y = x).
move/perm_cat2l/(_ (filter (pred1 x) s))/perm_eq_trans => @/s'.
move/(_ _ (perm_filterC (pred1 x) s)); rewrite filter_pred1.
rewrite flatten_cons => /perm_eqlP; rewrite perm_eq_sym=> <-.
apply/perm_cat2l/perm_eq_refl_eq; congr; apply/eq_in_map.
move=> a ta /=; case: (x = a)=> [->>//|] ne_xa.
congr; rewrite count_filter; apply/eq_count.
by move=> b; apply/andb_idr=> -> @/predC1; rewrite eq_sym.
qed.

lemma nosmt uniq_flatten_map (f : 'a -> 'b list) s:
  (forall x, uniq (f x)) =>
  (forall x y, mem s x => mem s y => has (mem (f x)) (f y) => x = y) =>
  uniq s => uniq (flatten (map f s)).
proof.
move=> uqf; elim: s => /= [|x s ih inj_f [Nsx uqs]].
  by rewrite flatten_nil.
rewrite flatten_cons cat_uniq; rewrite uqf ih //=.
  by move=> a b sa sb; apply/inj_f; rewrite (sa, sb).
apply/negP=> /hasP [a] [/flatten_mapP] [b] [sb] fba fxa.
have ->>//: x = b; apply/inj_f=> //; first by rewrite sb.
by apply/hasP; exists a.
qed.

lemma count_flatten_nseq (p : 'a -> bool) k s :
  count p (flatten (nseq k s)) = (max 0 k) * (count p s).
proof.
case: (lez_total 0 k) => [ge0_k|le0_k]; last first.
  by rewrite (_ : max 0 k = 0) 1:/# //= nseq0_le // flatten_nil.
rewrite (_ : max 0 k = k) 1:/#  //; elim: k ge0_k => [|k ge0_k ih].
  by rewrite nseq0 flatten_nil.
by rewrite nseqS // flatten_cons count_cat /#.
qed.

lemma nosmt perm_eq_pair ['a 'b] (s : ('a * 'b) list) : uniq s => perm_eq s
  (flatten
     (map (fun a => filter (fun xy : _ * _ => xy.`1 = a) s)
          (undup (map fst s)))).
proof.
move=> uq_s; apply: uniq_perm_eq => //=.
+ apply: uniq_flatten_map => /=.
  * by move=> x; rewrite filter_uniq.
  * move=> x y; rewrite !mem_undup => /mapP[] [/=] a1 b1 [_ ->].
    case/mapP=> -[/=] a2 b2 [_ ->] /hasP[] [a b] /=.
    by rewrite !mem_filter /= => -[] [-> _] [-> _].
  * by apply: undup_uniq.
case=> a b; split => [ab_in_s|].
+ apply/flatten_mapP; exists a; rewrite mem_undup /= ?mem_filter //=.
  by rewrite ab_in_s /= &(mapP); exists (a, b).
case/flatten_mapP=> a'; rewrite mem_undup => -[] /mapP[].
by case=> a2 b2 /= [_ ->>]; rewrite mem_filter /=.
qed.

(* -------------------------------------------------------------------- *)
(*                               Mask                                   *)
(* -------------------------------------------------------------------- *)
op mask ['a] m (s : 'a list) =
  with m = []    , s = []     => []
  with m = b :: m, s = []     => []
  with m = []    , s = x :: s => []
  with m = b :: m, s = x :: s =>
    if b then x :: mask m s else mask m s.

lemma mask0 m : mask m [] = [<:'a>].
proof. by case: m. qed.

lemma mask_false s n : mask (nseq n false) s = [<:'a>].
proof.
elim: s n => [|x s ih] n; first by rewrite mask0.
elim/natcase: n => n hn; first by rewrite nseq0_le.
by rewrite nseqS //= ih.
qed.

lemma mask_true (s : 'a list) n :
  size s <= n => mask (nseq n true) s = s.
proof.
elim: s n => /= [|x s ih] n le; first by rewrite mask0.
elim/natcase: n le => n hn; first move/lez_trans/(_ _ hn).
  by rewrite addzC -ltzE ltzNge size_ge0.
by rewrite addzC lez_add2r nseqS //= => /ih ->.
qed.

lemma mask_cons b m x s :
  mask<:'a> (b :: m) (x :: s) = nseq (b2i b) x ++ mask m s.
proof. by case: (b) => _; rewrite (nseq0, nseq1). qed.

lemma size_mask m s :
  size m = size s => size (mask<:'a> m s) = count idfun m.
proof.
move: m s; apply/seq2_ind => //= x1 x2 s1 s2 ih.
by case: (x1) => /=; rewrite ih.
qed.

lemma mask_cat m1 m2 s1 s2 : size m1 = size s1 =>
  mask<:'a> (m1 ++ m2) (s1 ++ s2) = mask m1 s1 ++ mask m2 s2.
proof. by move: m1 s1; apply/seq2_ind=> //= -[]. qed.

(* -------------------------------------------------------------------- *)
(*                             Subseq                                   *)
(* -------------------------------------------------------------------- *)
op subseq (s1 s2 : 'a list) =
  with s2 = []      , s1 = []       => true
  with s2 = []      , s1 = _ :: _   => false
  with s2 = x :: s2', s1 = []       => true
  with s2 = x :: s2', s1 = y :: s1' =>
    subseq (if x = y then s1' else s1) s2'.

lemma sub0seq (s : 'a list) : subseq [] s.
proof. by case: s. qed.

lemma subseq0 (s : 'a list) : subseq s [] = (s = []).
proof. by case: s. qed.

lemma subseqP (s1 s2 : 'a list) :
      (exists m, size m = size s2 /\ s1 = mask m s2)
  <=> (subseq s1 s2).
proof.
elim: s2 s1 => [|y s2 ih] [|x s1] /=; last (split; last first).
+ by exists [].
+ by apply/negP; do 2! case.
+ exists (nseq (size s2 + 1) false); rewrite ?mask_false /=.
  by rewrite size_nseq; smt(size_ge0).
+ case/ih=> m [eqsz def]; exists ((y = x) :: m) => //=.
  by rewrite eqsz /=; case _: (y = x) def => /= [!->|].
case: (y = x) => [->>|ne_yx]; last first.
  case=> -[//|[] m] /= [/addzI eq_sz] => [[/eq_sym ?]|] //.
  by move=> ->; apply/ih; exists m.
case=> m [eqsz eq]; pose i := index true m; apply/ih.
have def: take i m = nseq (size (take i m)) false.
  apply/all_pred1P/(all_nthP _ _ true)=> j [ge0_j lt] @/pred1.
  have {lt}lt_ji: j < i; first move: lt.
    rewrite size_take ?index_ge0; case: (i < size m) => //.
    by rewrite ltzNge !ltzE => /= h1 h2; apply/(lez_trans (size m)).
  rewrite nth_take ?index_ge0 //; have := (before_find true (pred1 true)).
  by move/(_ m j); rewrite lt_ji ge0_j /pred1 /=; case: (nth _ _ _).
have lt_im: i < size m.
  rewrite ltzNge; apply/negP=> le_mi; move: def eq.
  by rewrite take_oversize // => ->; rewrite mask_false.
exists (take i m ++ drop (i+1) m); split.
  rewrite size_cat ?(size_take, size_drop).
    by rewrite index_ge0. by rewrite addz_ge0 ?index_ge0.
  by rewrite lt_im /=; smt(size_ge0).
have /= -> := congr1 behead _ _ eq; rewrite -(cat_take_drop i s2).
rewrite -{1}(cat_take_drop i m) def -cat_cons.
have sz_i_s2: size (take i s2) = i.
  by rewrite &(size_takel) index_ge0 /= /#.
have h: size (take i m) = size (take i s2).
+ by rewrite sz_i_s2 size_takel // index_ge0 /= ltzW.
rewrite lastI cat_rcons !mask_cat ?size_nseq ?size_belast.
+ by rewrite h; smt(size_ge0). + by rewrite h; smt(size_ge0).
rewrite !mask_false (drop_nth true) ?index_ge0 //.
by rewrite nth_index -?index_mem.
qed.

lemma cat_subseq (s1 s2 s3 s4 : 'a list) :
  subseq s1 s3 => subseq s2 s4 => subseq (s1 ++ s2) (s3 ++ s4).
proof.
case/subseqP=> m1 [sz_m1 ->] /subseqP [m2] [sz_m2 ->].
apply/subseqP; exists (m1 ++ m2); rewrite !size_cat.
by rewrite !mask_cat // sz_m1 sz_m2.
qed.

lemma subseq_refl (s : 'a list) : subseq s s.
proof. by elim: s => //= x s IHs; rewrite eqxx. qed.

lemma subseq_trans (s2 s1 s3 : 'a list) :
  subseq s1 s2 => subseq s2 s3 => subseq s1 s3.
proof.
move=> /subseqP[m2] [h{h} ->] /subseqP[m1] [h{h} ->].
elim: s3 m1 m2 => [|x s ih] m1 m2; first by rewrite !mask0.
case: m1 => [|[] m1]; first by rewrite mask0.
  case: m2 => [|[] m2] //=; first by rewrite /= ih.
  case/subseqP: (ih m1 m2) => m [sz_m def_s]; apply/subseqP.
  by exists (false :: m); rewrite //= sz_m.
case/subseqP: (ih m1 m2) => m [sz_m def_s]; apply/subseqP.
by exists (false :: m); rewrite //= sz_m.
qed.

lemma subseq_cons (s : 'a list) x : subseq s (x :: s).
proof. by apply/(@cat_subseq [] s [x] s)=> //; apply/subseq_refl. qed.

lemma subseq_rcons (s : 'a list) x : subseq s (rcons s x).
proof. by rewrite -{1}(@cats0 s) -cats1 cat_subseq // subseq_refl. qed.

lemma rem_subseq x (s : 'a list) : subseq (rem x s) s.
proof.
elim: s => //= y s ih; rewrite eq_sym.
by case: (x = y) => //= _; apply/subseq_cons.
qed.

lemma filter_subseq a (s : 'a list) : subseq (filter a s) s.
proof.
elim: s => //= y s ih; case: (a y)=> //= Nay.
by apply/(subseq_trans s)/subseq_cons/ih.
qed.

lemma count_subseq ['a] (p : 'a -> bool) s1 s2 : subseq s1 s2 =>
  count p s1 <= count p s2.
proof.
elim: s2 s1 => [|y s2 ih] [|x s1] //=.
+ by rewrite addz_ge0 ?(count_ge0, b2i_ge0).
+ by case: (y = x) => [-> /ih|? /ih] /#.
qed.

(* -------------------------------------------------------------------- *)
(*                            All pairs                                 *)
(* -------------------------------------------------------------------- *)
op zip ['a 'b] (s : 'a list) (t : 'b list) =
  with s = x :: s', t = y :: t' => (x, y) :: zip s' t'
  with s = _ :: _ , t = []      => []
  with s = []     , t = _ :: _  => []
  with s = []     , t = []      => [].

abbrev unzip1 ['a 'b] (s : ('a * 'b) list) = map fst s.
abbrev unzip2 ['a 'b] (s : ('a * 'b) list) = map snd s.

abbrev amap ['a 'b 'c] (f : 'a -> 'b -> 'c) (xs : ('a * 'b) list) =
  map (fun xy => (fst xy, f (fst xy) (snd xy))) xs.

lemma zip_unzip ['a 'b] (s : ('a * 'b) list) :
  zip (unzip1 s) (unzip2 s) = s.
proof. by elim: s => // -[x y s]. qed.

lemma unzip1_zip ['a 'b] (s : 'a list) (t : 'b list) :
  size s <= size t => unzip1 (zip s t) = s.
proof.
elim: s t => [|x s ih] [|y t] //=; 1: smt(size_ge0).
by rewrite lez_add2l => /ih ->.
qed.

lemma unzip2_zip ['a 'b] (s : 'a list) (t : 'b list) :
  size t <= size s => unzip2 (zip s t) = t.
proof.
elim: s t => [|x s ih] [|y t] //=; 1: smt(size_ge0).
by rewrite lez_add2l => /ih ->.
qed.

lemma size1_zip ['a 'b] (s : 'a list) (t : 'b list) :
  size s <= size t => size (zip s t) = size s.
proof.
elim: s t => [|x s ih] [|y t] //=; 1: smt(size_ge0).
by rewrite lez_add2l => /ih ->.
qed.

lemma size2_zip ['a 'b] (s : 'a list) (t : 'b list) :
  size t <= size s => size (zip s t) = size t.
proof.
elim: s t => [|x s ih] [|y t] //=; 1: smt(size_ge0).
by rewrite lez_add2l => /ih ->.
qed.

lemma size_zip ['a 'b] (s : 'a list) (t : 'b list) :
  size (zip s t) = min (size s) (size t).
proof. by elim: s t => [|x s ih] [|y t] //=; smt(size_ge0). qed.

lemma zip_cat ['a 'b] (s1 s2 : 'a list) (t1 t2 : 'b list) :
  size s1 = size t1 => zip (s1 ++ s2) (t1 ++ t2) = zip s1 t1 ++ zip s2 t2.
proof. elim: s1 t1 => [|x s1 ih] [|y t1] //=; smt(size_ge0). qed.

lemma nth_zip ['a 'b] (x : 'a) (y : 'b) s t i :
  size s = size t => nth (x, y) (zip s t) i = (nth x s i, nth y t i).
proof. by elim: s t i => [|xs s ih] [|xt t] //=; smt(size_ge0). qed.

lemma nth_zip_cond ['a 'b] p (s : 'a list) (t : 'b list) i :
   nth p (zip s t) i
     = (if i < size (zip s t) then (nth p.`1 s i, nth p.`2 t i) else p).
proof.
case: (i < 0) => [le0_i|].
+ by rewrite !nth_neg // -(pairS p) if_same.
by elim: s t i => [|x s ih] [|y t] i //=; (move=> ->// || smt(size_ge0)).
qed.

lemma zip_rcons ['a 'b] s1 s2 (z1 : 'a) (z2 : 'b) :
  size s1 = size s2 =>
    zip (rcons s1 z1) (rcons s2 z2) = rcons (zip s1 s2) (z1, z2).
proof. by move=> eq_sz; rewrite -!cats1 zip_cat //= eq_sz. qed.

lemma rev_zip ['a 'b] (s1 : 'a list) (s2 : 'b list) :
  size s1 = size s2 => rev (zip s1 s2) = zip (rev s1) (rev s2).
proof.
elim: s1 s2 => [|x s1 ih] [|y s2] //=; 1,2,3: smt(size_ge0).
by move/addzI=> eq_sz; rewrite !(rev_cons, zip_rcons) ?size_rev // ih.
qed.

lemma mem_zip ['a 'b] xs ys (x : 'a) (y : 'b):
  (x, y) \in zip xs ys => x \in xs /\ y \in ys.
proof.
by elim: xs ys => [|x0 xs ih] [|y0 ys] //=; case=> [|/ih] [] 2!->.
qed.

lemma nosmt mem_zip_fst ['a 'b] (xs : 'a list) (ys : 'b list) xy:
  xy \in zip xs ys => fst xy \in xs.
proof. by case: xy => [x y]; move/mem_zip. qed.

lemma nosmt mem_zip_snd ['a 'b] (xs : 'a list) (ys : 'b list) xy:
  xy \in zip xs ys => snd xy \in ys.
proof. by case: xy => [x y]; move/mem_zip. qed.

lemma zip_map ['a1 'a2 'b1 'b2] (f : 'a1 -> 'a2) (g : 'b1 -> 'b2) xs ys :
    zip (map f xs) (map g ys)
  = map (fun xy => (f (fst xy), g (snd xy))) (zip xs ys).
proof. by elim: xs ys => [|x xs ih] [|y ys] //=; rewrite ih. qed.

lemma zip_mapl ['a1 'a2 'b] (f : 'a1 -> 'a2) xs (ys : 'b list) :
  zip (map f xs) ys = map (fun xy => (f (fst xy), snd xy)) (zip xs ys).
proof. by rewrite -(@map_id ys) zip_map map_id. qed.

lemma zip_mapr ['a 'b1 'b2] (g : 'b1 -> 'b2) (xs : 'a list) ys :
  zip xs (map g ys) = map (fun xy => (fst xy, g (snd xy))) (zip xs ys).
proof. by rewrite -(@map_id xs) zip_map map_id. qed.

lemma assoc_zip ['a, 'b] (ks : 'a list) (vs : 'b list) k:
 size ks = size vs => assoc (zip ks vs) k = onth vs (index k ks).
proof.
elim: ks vs => [|k' ks ih] [|v vs] //=; rewrite ?(assoc_cons, index_cons).
+ by rewrite eq_sym addzC addz1_neq0.
move/addzI => /ih -> /=; case: (k = k') => //=.
by rewrite addz1_neq0 1:index_ge0.
qed.

lemma map_fst_zip ['a1, 'a2, 'b] (f : 'a1 -> 'a2) xs (ys : 'b list) :
 size xs = size ys => map (f \o fst) (zip xs ys) = map f xs.
proof. by move => eq_sz; rewrite map_comp unzip1_zip // eq_sz. qed.

lemma map_snd_zip ['a, 'b1, 'b2] (g : 'b1 -> 'b2) (xs : 'a list) ys :
 size xs = size ys => map (g \o snd) (zip xs ys) = map g ys.
proof. by move => eq_sz; rewrite map_comp unzip2_zip // eq_sz. qed.

lemma nosmt zip_map_proj ['a, 'b, 'c] (f : 'a -> 'b * 'c) xs:
  zip (map (fst \o f) xs) (map (snd \o f) xs) = map f xs.
proof. by elim: xs => // x xs ih @/(\o) /=; rewrite ih /=; case: (f x). qed.

lemma nosmt onth_zip_some ['a 'b] (xs : 'a list) (ys : 'b list) n xy:
      onth (zip xs ys) n = Some xy
  <=> (onth xs n = Some (fst xy)) /\ (onth ys n = Some (snd xy)).
proof.
elim: xs ys n => [|x xs ih] [|y ys] n //=; case: xy ih => [x' y'] ih.
by case: (n = 0) => // _; apply/ih.
qed.

lemma nosmt eq_keys_amap ['a, 'b1, 'b2, 'c]
  (f : 'a -> 'b1 -> 'c) (g : 'a -> 'b2 -> 'c) xs ys
: amap f xs = amap g ys => unzip1 xs = unzip1 ys.
proof. move=> eq_amap.
have ->: (map fst xs) = (map fst (amap f xs)) by rewrite -map_comp.
have ->: (map fst ys) = (map fst (amap g ys)) by rewrite -map_comp.
by rewrite eq_amap.
qed.

lemma assoc_amap ['a, 'b, 'c] (f : 'a -> 'b -> 'c) xs k:
 assoc (amap f xs) k = omap (f k) (assoc xs k).
proof.
elim: xs => /= [|[k' v'] xs ih]; 1: by rewrite !assoc_nil.
by rewrite !assoc_cons /=; case: (k = k').
qed.

lemma nosmt map_zip_nth ['a, 'b, 'c] dk dv (f: 'a * 'b -> 'c) ks vs:
 size ks = size vs => map f (zip ks vs)
   = map (fun i => f (nth dk ks i, nth dv vs i)) (range 0 (size ks)).
proof.
move=> eq_sz; rewrite -(@map_nth_range (dk, dv) (zip ks vs)).
rewrite /range /= size_zip /min eq_sz //= -map_comp.
by apply: eq_in_map => i @/(\o); rewrite mem_iota /= nth_zip.
qed.

lemma amap_assoc_zip ['a, 'b, 'c] (f : 'a -> 'b -> 'c) ks vs:
 size ks = size vs => uniq ks => amap f (zip ks vs) =
   amap (fun k _ => f k (nth witness vs (index k ks))) (zip ks vs).
proof.
move=> eq_sz uq_ks; rewrite (map_zip_nth witness witness) //= eq_sym.
rewrite (map_zip_nth witness witness) //= &(eq_in_map).
by move=> x /mem_range [? ?] /=; congr; rewrite index_uniq.
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
    elim: s => //= y s IHs; case: (e x y) => exy.
      by rewrite perm_cons perm_eq_refl.
    by rewrite perm_consCA perm_cons.
  qed.

  lemma nosmt perm_sort (e : 'a -> 'a -> bool) s: perm_eq (sort e s) s.
  proof.
    elim: s=> //= x s IHs; cut h := perm_insert e x (sort e s).
    by apply perm_eqlE in h; rewrite -h perm_cons => {h}.
  qed.

  lemma nosmt sorted_insert (e : 'a -> 'a -> bool) x s:
       (forall x y, e x y \/ e y x)
    => sorted e s => sorted e (insert e x s).
  proof.
    move=> e_ltgt; case: s => //= y s; case: (e x y) => [-> -> // |].
    elim: s x y => /= [|z s IHs] x y; first by smt.
    move=> Nexy [eyz pt_zs]; case: (e x z); first by smt.
    by move=> Nexz; rewrite eyz /= IHs.
  qed.

  lemma nosmt sort_sorted (e : 'a -> 'a -> bool) (s : 'a list):
     (forall x y, e x y \/ e y x) => sorted e (sort e s).
  proof. by move=> e_ltgt; elim: s => //= x s IHs; apply sorted_insert. qed.
end InsertSort.

op sort (e : 'a -> 'a -> bool) s = InsertSort.sort e s axiomatized by sortE.

lemma perm_sort e (s : 'a list): perm_eq (sort e s) s.
proof. by rewrite sortE /=; apply InsertSort.perm_sort. qed.

lemma sort_sorted (e : 'a -> 'a -> bool) s:
  (forall (x y : 'a), e x y \/ e y x) => sorted e (sort e s).
proof. by rewrite sortE /=; apply InsertSort.sort_sorted. qed.

lemma subseq_order_path (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => forall (x : 'a) s1 s2,
       subseq s1 s2 => path e x s2 => path e x s1.
proof.
move=> e_tr x s1 s2; elim: s2 x s1 => [|y s2 ih] x [|z s1] //= /(ih y).
case: (y = z) => {ih} [->|_] ih[] /=; 1: by move=> ->.
by move=> e_xy /ih [] e_yz; move/e_tr: e_xy => /(_ z e_yz).
qed.

lemma subseq_sorted (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => forall s1 s2, subseq s1 s2 => sorted e s2 => sorted e s1.
proof.
move=> e_tr [|x1 s1] [|x2 s2] //= sub_s12.
move/(subseq_order_path e e_tr _ _ _ sub_s12).
by case: (x2 = x1)=> [->//| _[]].
qed.

lemma sorted_filter (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => forall a s, sorted e s => sorted e (filter a s).
proof.
by move=> e_tr a s; apply/(subseq_sorted e e_tr _ _ (filter_subseq a s)).
qed.

lemma sorted_rem (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => forall x s, sorted e s => sorted e (rem x s).
proof.
by move=> e_tr x s; apply/(subseq_sorted e e_tr _ _ (rem_subseq x s)).
qed.

lemma mem_sort e s (x : 'a) : mem (sort e s) x <=> mem s x.
proof. by apply/perm_eq_mem; rewrite perm_sort. qed.

lemma size_sort e (s : 'a list) : size (sort e s) = size s.
proof. by apply/perm_eq_size; rewrite perm_sort. qed.

lemma sort_uniq e (s : 'a list) : uniq (sort e s) <=> uniq s.
proof. by apply/perm_eq_uniq; rewrite perm_sort. qed.

lemma perm_sortl (e : 'a -> 'a -> bool) s :
  forall s', perm_eq (sort e s) s' <=> perm_eq s s'.
proof. by apply/perm_eqlP/perm_sort. qed.

lemma order_path_min (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => forall x s, path e x s => all (e x) s.
proof.
move=> e_tr x s; elim: s x => [|y s ih] x //= [^e_xy -> /ih /=].
by move/allP=> h; apply/allP=> z /h; apply/(e_tr y).
qed.

lemma path_sorted e (x : 'a) s : path e x s => sorted e s.
proof. by case: s => //= y s. qed.

lemma eq_sorted (e : 'a -> 'a -> bool) :
     (forall y x z, e x y => e y z => e x z)
  => (forall x y, e x y => e y x => x = y)
  => forall s1 s2, sorted e s1 => sorted e s2 =>
       perm_eq s1 s2 => s1 = s2.
proof.
move=> e_tr e_asym; elim=> [|x1 s1 ih] s2 ss1 ss2 eq12.
  by apply/perm_eq_small=> //; rewrite -(perm_eq_size _ _ eq12).
have s2_x1: mem s2 x1 by rewrite -(perm_eq_mem _ _ eq12) mem_head.
case: s2 s2_x1 eq12 ss2 => //= x2 s2 /=.
case: (x1 = x2) => [<- /= eq12 ss2|ne_x12 /= s2_x1 eq12].
  by rewrite (ih s2) ?(@path_sorted e x1) // -(perm_cons x1).
apply/negP=> ss2; have/negP := (ne_x12); apply; apply/e_asym; last first.
  by have /(_ _ _ ss2)/allP -> := order_path_min e e_tr.
have: mem (x1 :: s1) x2 by rewrite (perm_eq_mem _ _ eq12) mem_head.
rewrite /= eq_sym ne_x12 /= => s1_x2; rewrite /= in ss1.
by have /(_ _ _ ss1)/allP -> := order_path_min e e_tr.
qed.

lemma perm_sortP (e : 'a -> 'a -> bool):
     (forall x y, e x y \/ e y x)
  => (forall y x z, e x y => e y z => e x z)
  => (forall x y, e x y => e y x => x = y)
  => forall s1 s2, (perm_eq s1 s2) <=> (sort e s1 = sort e s2) .
proof.
move=> e_tt e_tr e_asym s1 s2; split=> eq12; last first.
  by have /perm_eqlP <- := perm_sort e s1; rewrite eq12 perm_sort.
apply/(eq_sorted e)=> //; rewrite ?sort_sorted //.
have /perm_eqlP -> := perm_sort e s1; have /perm_eqlP -> := eq12.
by apply/perm_eq_sym/perm_sort.
qed.

lemma sortK (e : 'a -> 'a -> bool) :
     (forall x y, e x y \/ e y x)
  => (forall y x z, e x y => e y z => e x z)
  => (forall x y, e x y => e y x => x = y)
  => forall s, sort e (sort e s) = sort e s.
proof.
move=> e_tot e_tr e_asym s; apply/(eq_sorted e e_tr e_asym).
  by apply/sort_sorted. by apply/sort_sorted.
by apply/perm_sort.
qed.

lemma sort_id (e : 'a -> 'a -> bool) :
     (forall x y, e x y \/ e y x)
  => (forall y x z, e x y => e y z => e x z)
  => (forall x y, e x y => e y x => x = y)
  => forall s, sorted e s => sort e s = s.
proof.
move=> e_tot e_tr e_asym s ss; apply/(eq_sorted e) => //.
  by apply/sort_sorted. by apply/perm_sort.
qed.

lemma sort_rem (e : 'a -> 'a -> bool) :
     (forall x y, e x y \/ e y x)
  => (forall y x z, e x y => e y z => e x z)
  => (forall x y, e x y => e y x => x = y)
  => forall x s,  mem s x =>
       exists s1 s2, sort e s = s1 ++ x :: s2
        /\ sort e (rem x s) = s1 ++ s2.
proof.
move=> e_tot e_tr e_asym x s ^sx /perm_to_rem eqs.
have ^ssx: mem (sort e s) x by rewrite mem_sort sx.
case/splitPr=> s1 s2 ^eqss ->; exists s1 s2 => //=.
have ss: sorted e (s1 ++ x :: s2) by rewrite -eqss sort_sorted.
have ss12 := subseq_sorted e e_tr (s1 ++ s2) _ _ ss.
  by apply/cat_subseq/subseq_cons; apply/subseq_refl.
have /(_ _ ss12) <- // := sort_id e e_tot e_tr e_asym.
apply/(@eq_sorted e)=> //; try by apply/sort_sorted.
apply/perm_eqlP=> s'; rewrite !perm_sortl; apply/perm_eqlP.
rewrite -(perm_cat2l [x]) perm_eq_sym perm_catCl perm_catAC -catA /=.
by rewrite -eqss (@perm_eq_trans s) // perm_sort.
qed.

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
