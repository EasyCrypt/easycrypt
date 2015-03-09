(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

require import Option Int NewList.
pragma +implicits.

(* -------------------------------------------------------------------- *)
type 'a array = 'a list.

op "_.[_]": 'a array -> int -> 'a = nth witness
  axiomatized by getE.

lemma arrayP (a1 a2 : 'a array):
  (a1 = a2) <=>
  size a1 = size a2 /\ (forall i, 0 <= i < size a2 => a1.[i] = a2.[i]).
proof.
  split=> [-> //= | []].
  elim a2 a1=> /=.
    by move=> a1; rewrite size_eq0=> ->.
  move=> x xs ih [//= | //= x' xs' /addzI eq_sizes h].
    by rewrite eq_sym addzC addz1_neq0 1:size_ge0.
  split.
    by have //= := h 0 _; rewrite ?getE //= -lez_add1r lez_addl size_ge0.
  apply ih=> //.
  move=> i [le0_i lti_lenxs]; have:= h (i + 1) _.
    smt. (* side conditions... *)
  by rewrite getE /= addz1_neq0 //= addAzN.
qed.

(* -------------------------------------------------------------------- *)
op "_.[_<-_]" (xs : 'a array) (n : int) (a : 'a) =
  with xs = "[]"      => []
  with xs = (::) x xs => if   n = 0
                         then a::xs
                         else x::(xs.[n - 1 <- a]).

lemma size_set (xs : 'a array) (n : int) (a : 'a):
  size xs.[n <- a] = size xs.
proof. by elim xs n => //= x xs ih n; case (n = 0)=> //=; rewrite ih. qed.

lemma set_out (n : int) (a : 'a) (xs : 'a array):
  n < 0 \/ size xs <= n =>
  xs.[n <- a] = xs.
proof.
  elim xs n=> //= x xs ih n.
  move=> h; have -> /=: n <> 0 by smt.
  case {-1}(n < 0) (eq_refl (n < 0)) h=> //= [lt0_n | ].
    by apply ih; left; smt.
  rewrite neqF ltzNge /= => le0_n lt_xs_n.
  by apply ih; right; smt.
qed.

lemma nth_set (n n': int) (a : 'a) (xs : 'a array):
  0 <= n  < size xs =>
  0 <= n' < size xs =>
  xs.[n <- a].[n'] = if n' = n then a else xs.[n'].
proof.
  move=> n_bounds n'_bounds.
  rewrite getE; elim xs n n_bounds n' n'_bounds=> //=.
    smt.
  move=> x xs ih n n_bounds n' n'_bounds.
  case (n = 0)=> //= [->> | ].
    by case (n' = 0).
  case (n' = 0)=> //=.
    by move=> ->>; rewrite eq_sym=> ->.
  move=> ne_n'_0 ne_n_0; rewrite ih 1..2:smt.
  by have ->: (n' - 1 = n - 1) = (n' = n) by smt.
qed.

lemma get_set (xs : 'a array) (n n' : int) (x : 'a):
  xs.[n <- x].[n'] =
    if   (0 <= n < size xs /\ n' = n)
    then x
    else xs.[n'].
proof.
  case (0 <= n' < size xs).
    case (0 <= n < size xs)=> /=.
      by apply nth_set.
    have ->: (0 <= n < size xs) <=> (0 <= n /\ n < size xs) by done.
    by rewrite -nand -ltzNge /= @(ltzNge _ (size xs)) /= => /set_out ->.
  have ->: (0 <= n' < size xs) <=> (0 <= n' /\ n' < size xs) by done.
  rewrite -nand -ltzNge /= @(ltzNge _ (size xs)) /= => [n'_lt0 | lt_n'_xs].
    by rewrite getE !nth_neg //; case (0 <= n < size xs)=> //=; smt.
  by rewrite getE !nth_default ?size_set //; case (0 <= n < size xs)=> //=; smt.
qed.

lemma set_set (xs : 'a array) (n n' : int) (x x' : 'a):
  forall i,
    xs.[n <- x].[n' <- x'].[i] =
      if   n = n'
      then xs.[n' <- x'].[i]
      else xs.[n' <- x'].[n <- x].[i].
proof.
  case (n = n')=> [->> /= |].
    move=> i; rewrite !get_set; case (i = n')=> //=.
    by rewrite size_set; case (0 <= n' < size xs).
  move=> ne_n_n' i; case (i = n')=> [->> /= {i} |].
    by rewrite !get_set /= @(eq_sym n') ne_n_n' /= size_set.
  move=> ne_i_n'; case (i = n)=> [->> /= {i} |].
    by rewrite !get_set /= ne_n_n' /= size_set.
  by move=> ne_i_n; rewrite !get_set ne_i_n ne_i_n'.
qed.

lemma set_set_eq (xs : 'a array) (n : int) (x x' : 'a):
  forall i, xs.[n <- x].[n <- x'].[i] = xs.[n <- x'].[i].
proof. by move=> i; rewrite set_set. qed.

(* -------------------------------------------------------------------- *)
op make (l : int) (x : 'a) = mkseq (fun i => x) l
  axiomatized by makeE.

lemma size_make l (x:'x):
  size (make l x) = max 0 l.
proof. by rewrite makeE; apply size_mkseq. qed.

lemma get_make l (x:'x) i:
  0 <= i < l => (make l x).[i] = x. (* FIXME *)
proof. by rewrite makeE getE; apply @(nth_mkseq _ (fun i => x)). qed.

(* -------------------------------------------------------------------- *)
op init (l : int) (f : int -> 'a) = mkseq f l
  axiomatized by initE.

lemma size_init l (f:int -> 'x):
  size (init l f) = max 0 l.
proof. by rewrite initE; apply size_mkseq. qed.

lemma get_init l (f:int -> 'x) i:
  0 <= i < l => (init l f).[i] = f i.
proof. by rewrite initE getE; apply nth_mkseq. qed.

lemma make_init n (a:'a) : init n (fun x => a) = make n a.
proof.
  rewrite arrayP size_init size_make /=.
  by move=> i le0_i_ltn; rewrite get_init 1:smt get_make 1:smt.
qed.

(* -------------------------------------------------------------------- *)
op sub (xs : 'x array) (s : int) (l : int) = take l (drop s xs)
  axiomatized by subE.

lemma size_sub (xs:'x array) (s l:int):
  0 <= s => 0 <= l => s + l <= size xs =>
  size (sub xs s l) = l.
proof.
  move=> le0_s le0_l le_sl_xs.
  rewrite subE size_take // size_drop //.
  smt.
qed.

lemma get_sub (xs:'x array) (s l i:int):
  0 <= s => 0 <= l => s + l <= size xs =>
  0 <= i < l =>
  (sub xs s l).[i] = xs.[i + s].
proof.
  move=> le0_s le0_l le_sl_xs [le0_i lt_i_l].
  by rewrite subE getE nth_take 3:nth_drop // addzC.
qed.
