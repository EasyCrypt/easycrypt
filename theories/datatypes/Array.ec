(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Option Logic Fun Int List.

(* -------------------------------------------------------------------- *)
type 'a array.

op mkarray : 'a list -> 'a array.
op ofarray : 'a array -> 'a list.

axiom nosmt mkarrayK : cancel ofarray<:'a> mkarray.
axiom nosmt ofarrayK : cancel mkarray<:'a> ofarray.

lemma nosmt arrayW (P : 'a array -> bool):
     (forall s, P (mkarray s))
  => forall n, P n.
proof. by move=> ih n; rewrite -mkarrayK; apply/ih. qed.

lemma nosmt mkarray_inj: injective mkarray<:'a>.
proof. by apply/(can_inj _ _ ofarrayK). qed.

lemma nosmt ofarray_inj: injective ofarray<:'a>.
proof. by apply/(can_inj _ _ mkarrayK). qed.

(* -------------------------------------------------------------------- *)
op size (arr : 'a array) = size (ofarray arr)
axiomatized by sizeE.

op "_.[_]" (arr : 'a array) (i : int) = nth witness (ofarray arr) i
axiomatized by getE.

op "_.[_<-_]" (arr : 'a array) (i : int) (x : 'a) =
  mkarray (mkseq (fun k => if i = k then x else arr.[k]) (size arr))
axiomatized by setE.

(* -------------------------------------------------------------------- *)
lemma size_ge0 (arr : 'a array): 0 <= size arr.
proof. by rewrite sizeE size_ge0. qed.

lemma size_mkarray (s : 'a list): size (mkarray s) = size s.
proof. by rewrite sizeE ofarrayK. qed.

(* -------------------------------------------------------------------- *)
(* FIXME: name scheme copied from List.nth. It looks ridiculous. *)
lemma nosmt get_neg (arr : 'a array) (i : int):
  i < 0 => arr.[i] = witness.
proof. by rewrite getE; apply/nth_neg. qed.

lemma nosmt get_default (arr : 'a array) (i : int):
  size arr <= i => arr.[i] = witness.
proof. rewrite getE sizeE; apply/nth_default. qed.

lemma nosmt arrayP (arr1 arr2 : 'a array):
  arr1 = arr2 <=>
  (size arr1 = size arr2
   /\ (forall i, 0 <= i < size arr1 => arr1.[i] = arr2.[i])).
proof.
split=> [//|[size_eq eq_get]].
apply/ofarray_inj/(eq_from_nth witness)=> [|i]; rewrite -!sizeE//.
+ by rewrite -!getE=> /eq_get.
qed.

lemma nosmt eq_from_get (arr1 arr2 : 'a array):
  size arr1 = size arr2 =>
  (forall i, 0 <= i < size arr1 => arr1.[i] = arr2.[i]) =>
  arr1 = arr2.
proof. by move=> eq_size eq_get; apply/arrayP. qed.

(* -------------------------------------------------------------------- *)
lemma get_set_if (arr : 'a array) (x : 'a) (i j : int):
  arr.[i <- x].[j] = if 0 <= i < size arr /\ j = i then x else arr.[j].
proof.
elim/arrayW: arr=> arr; rewrite !(setE, getE, size_mkarray, ofarrayK).
rewrite nth_mkseq_if (eq_sym j).
case: (0 <= j < size arr)=> [|^j_out /(nth_out witness) ->].
+ by case: (i = j)=> //= [-> -> //|]; rewrite getE ofarrayK.
+ by case: (i = j)=> [->|//=]; rewrite j_out.
qed.

(* -------------------------------------------------------------------- *)
lemma get_set (arr : 'a array) (x : 'a) (i j : int): 0 <= i < size arr =>
  arr.[i <- x].[j] = if j = i then x else arr.[j].
proof. by move=> lt_in; rewrite get_set_if lt_in. qed.

(* -------------------------------------------------------------------- *)
lemma size_set (arr : 'a array) (x : 'a) (i : int):
  size arr.[i <- x] = size arr.
proof.
rewrite setE size_mkarray size_mkseq /max.
by have /lez_eqVlt [->//=|->//=]:= size_ge0 arr.
qed.

(* -------------------------------------------------------------------- *)
lemma set_out (i : int) (x : 'a) (arr : 'a array):
  ! (0 <= i < size arr) => arr.[i <- x] = arr.
proof.
move=> Nlt_in; apply/arrayP; rewrite size_set//=.
by move=> j; rewrite get_set_if Nlt_in.
qed.

(* -------------------------------------------------------------------- *)
lemma set_neg (i : int) (a : 'a) (arr : 'a array):
  i < 0 => arr.[i<- a] = arr.
proof. by move=> lt0_i; rewrite set_out // lezNgt lt0_i. qed.

(* -------------------------------------------------------------------- *)
lemma set_above (i : int) (a : 'a) (arr : 'a array):
  size arr <= i => arr.[i <- a] = arr.
proof. by move=> le_ni; rewrite set_out // ltzNge le_ni. qed.

(* -------------------------------------------------------------------- *)
lemma set_set_if (arr : 'a array) (k k' : int) (x x' : 'a):
       arr.[k <- x].[k' <- x']
    =  if   k = k'
       then arr.[k' <- x']
       else arr.[k' <- x'].[k <- x].
proof.
apply/arrayP; split; rewrite !size_set.
  by rewrite fun_if; rewrite !size_set if_same.
move=> i lt_in; case: (0 <= k < size arr)=> [lt_ksz|]; last first.
  by move=> ?; rewrite !(set_out k) ?size_set.
case: (0 <= k' < size arr)=> [lt_k'sz|]; last first.
  by move=> ?; rewrite !(set_out k') ?size_set //; case: (k = k').
rewrite fun_if2; rewrite !get_set ?size_set //.
case: (k = k') => [->>|]; first by case: (i = k').
by case: (i = k') => //; case: (i = k).
qed.

(* -------------------------------------------------------------------- *)
lemma set_set_eq (arr : 'a array) (k : int) (x x' : 'a):
  arr.[k <- x].[k <- x'] = arr.[k <- x'].
proof. by rewrite set_set_if. qed.

(* -------------------------------------------------------------------- *)
lemma set_set_swap (arr : 'a array) (k k' : int) (x x' : 'a):
  k <> k => arr.[k <- x].[k' <- x'] = arr.[k' <- x'].[k' <- x'].
proof. by rewrite set_set_if. qed.

(* -------------------------------------------------------------------- *)
op offun f n: 'a array = mkarray (mkseq f n).

lemma offunifE (f : int -> 'a) n i:
  (offun f n).[i] = if 0 <= i < n then f i else witness.
proof. by rewrite getE ofarrayK nth_mkseq_if. qed.

lemma offunE n (f : int -> 'a) i: 0 <= i < n => (offun f n).[i] = f i.
proof. by move=> lt_in; rewrite offunifE lt_in. qed.

lemma size_offun (f : int -> 'a) n: size (offun f n) = max 0 n.
proof. by rewrite size_mkarray size_mkseq. qed.

(* -------------------------------------------------------------------- *)
op map (f : 'a -> 'b) (arr : 'a array) : 'b array =
  mkarray (map f (ofarray arr)).

lemma mapE (f : 'a -> 'b) arr i: 0 <= i < size arr =>
  (map f arr).[i] = f arr.[i].
proof.
elim/arrayW: arr => arr; rewrite size_mkarray !getE !ofarrayK.
by apply/nth_map.
qed.

lemma size_map (f : 'a -> 'b) arr: size (map f arr) = size arr.
proof. by rewrite size_mkarray size_map sizeE. qed.