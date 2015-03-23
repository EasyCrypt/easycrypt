(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B licence.
 * -------------------------------------------------------------------- *)

require import Pair.
require import Int.

(** Type declaration and core definitions *)
(* We could use the type of arrays, but would then require an additional validity condition *)
type 'a matrix.

op size: 'a matrix -> (int * int).

axiom size_pos: forall (M:'a matrix),
  0 <= fst (size M) /\ 0 <= snd (size M).

op "_.[_]": 'a matrix -> (int * int) -> 'a.

pred (==) (M0 M1:'a matrix) =
  size M0 = size M1 /\
  forall (i j:int),
    0 <= i => i < fst (size M0) =>
    0 <= j => j < snd (size M0) =>
    M0.[(i,j)] = M1.[(i,j)].

axiom extensionality: forall (M0 M1:'a matrix),
  M0 == M1 => M0 = M1.

(** Operators *)
(* new (m,n): allocates a new uninitialized (m,n) matrix *)
op new: (int * int) -> 'a matrix.

axiom new_size: forall m n,
  0 <= m => 0 <= n =>
  size (new<:'a> (m,n)) = (m,n).

(* set M (i,j) a: M.[(i,j) <- a] whenever (i,j) < size M [pairwise] *)
op "_.[_<-_]":  'a matrix -> (int * int) -> 'a -> 'a matrix.

axiom set_size: forall (M: 'a matrix) i j a,
  0 <= i => i < fst (size M) =>
  0 <= j => j < snd (size M) =>
  size (M.[(i,j) <- a]) = size M.

axiom set_get: forall (M:'a matrix) i j k l a,
  0 <= i => i < fst (size M) =>
  0 <= j => j < snd (size M) =>
  0 <= k => k < fst (size M) =>
  0 <= l => l < snd (size M) =>
  M.[(i,j) <- a].[(k,l)] = ((i,j) = (k,l)) ? a : M.[(k,l)].

(* sub M (i,j) (m,n): extracts the sub matrix of size (m,n) starting at (i,j) [whenever sizes fit] *)
op sub: 'a matrix -> (int * int) -> (int * int) -> 'a matrix.

axiom sub_size: forall (M:'a matrix) i j m n,
  0 <= i => 0 <= m => i + m <= fst (size M) =>
  0 <= j => 0 <= n => j + n <= snd (size M) =>
  size (sub M (i,j) (m,n)) = (m,n).

axiom sub_get: forall (M:'a matrix) i j m n k l,
  0 <= i => 0 <= m => i + m <= fst (size M) =>
  0 <= j => 0 <= n => j + n <= snd (size M) =>
  0 <= k => k < m =>
  0 <= l => l < n =>
  (sub M (i,j) (m,n)).[(k,l)] = M.[(i + k,j + l)].

(* write M (i,j) M' (k,l) (m,n): copy the contents of (sub M' (k,l) (m,n)) into M starting at index (i,j) *)
op write: 'a matrix -> (int * int) -> 
          'a matrix -> (int * int) -> (int * int) -> 'a matrix.

axiom write_size: forall (M M':'a matrix) i j k l m n,
  0 <= m => 0 <= n =>
  0 <= i => i + m <= fst (size M) =>
  0 <= j => j + n <= snd (size M) =>
  0 <= k => k + m <= fst (size M') =>
  0 <= l => l + n <= snd (size M') =>
  size (write M (i,j) M' (k,l) (m,n)) = size M.

axiom write_get: forall (M M':'a matrix) i j k l m n a b,
  0 <= m => 0 <= n =>
  0 <= i => i + m <= fst (size M) =>
  0 <= j => j + n <= snd (size M) =>
  0 <= k => k + m <= fst (size M') =>
  0 <= l => l + n <= snd (size M') =>
  0 <= a => a < fst (size M) =>
  0 <= b => b < snd (size M) =>
  (write M (i,j) M' (k,l) (m,n)).[(a,b)] =
    (i <= a /\ a < i + m /\ j <= b /\ b < j + n) ?
      M'.[(a - i + k,b - j + l)] :
      M.[(a,b)].

(* A small lemma to make sure I didn't get the definitions above too badly wrong *)
lemma write_sub: forall (M M':'a matrix) i j,
  0 <= i => i + fst (size M') <= fst (size M) =>
  0 <= j => j + snd (size M') <= snd (size M) =>
  sub (write M (i,j) M' (0,0) (size M')) (i,j) (size M') = M'.
proof -strict.
intros M M' i j i_0 i_bound j_0 j_bound.
apply extensionality; rewrite /(==);
pose m := fst (size M'); pose n := snd (size M'); cut ->: size M' = (m,n); first smt.
split.
  rewrite sub_size //=; smt.
  intros=> i' j' i'_pos i'_bnd j'_pos j'_bnd; rewrite sub_get //=; smt.
qed.

(* transpose M *)
op transpose: 'a matrix -> 'a matrix.

axiom transpose_size: forall (M:'a matrix),
  size (transpose M) = let (m,n) = size M in (n,m).

axiom transpose_get: forall (M:'a matrix) i j,
  0 <= i => i < snd (size M) =>
  0 <= j => j < fst (size M) =>
  (transpose M).[(i,j)] = M.[(j,i)].

lemma transpose_idempotent: forall (M:'a matrix),
  transpose (transpose M) = M.
proof -strict.
intros M; apply extensionality.
cut ext: (size (transpose (transpose M)) = size M &&
          forall i j, 0 <= i => i < fst (size M) => 0 <= j => j < snd (size M) =>
            (transpose (transpose M)).[(i,j)] = M.[(i,j)]) by split; smt.
smt.
qed.

(* Interactions with arrays *)
require Array.

(* Casting a one-row matrix to array *)
op to_array: 'a matrix -> 'a Array.array.

axiom to_array_length: forall (M:'a matrix),
  fst (size M) = 1 =>
  Array.length (to_array M) = snd (size M).

axiom to_array_get: forall (M:'a matrix) i,
  fst (size M) = 1 =>
  0 <= i => i < snd (size M) =>
  Array."_.[_]" (to_array M) i = M.[(i,0)].

(* Extracting a row *)
op row: 'a matrix -> int -> 'a Array.array.

axiom row_length: forall (M:'a matrix) j,
  0 <= j => j < snd (size M) =>
  Array.length (row M j) = fst (size M).

axiom row_get: forall (M:'a matrix) j i,
  0 <= j => j < snd (size M) =>
  0 <= i => i < fst (size M) =>
  Array."_.[_]" (row M j) i = M.[(i,j)].

(* Extracting a column *)
op column: 'a matrix -> int -> 'a Array.array.

axiom column_length: forall (M:'a matrix) i,
  0 <= i => i < fst (size M) =>
  Array.length (column M i) = snd (size M).

axiom column_get: forall (M:'a matrix) i j,
  0 <= i => i < fst (size M) =>
  0 <= j => j < snd (size M) =>
  Array."_.[_]" (column M i) j = M.[(i,j)].

lemma column_transpose_row: forall (M:'a matrix) i,
  0 <= i => i < snd (size M) =>
  row M i = column (transpose M) i.
proof -strict.
intros M i i_0 i_bound; apply Array.array_ext.
cut ext_eq: (Array.length (row M i) = fst (size M) /\
             Array.length (column (transpose M) i) = fst (size M) /\
             forall j, 0 <= j => j < fst (size M) =>
               Array."_.[_]" (row M i) j = M.[(j,i)] /\
               Array."_.[_]" (column (transpose M) i) j = (transpose M).[(i,j)] /\
               (transpose M).[(i,j)] = M.[(j,i)]); last by smt.
progress=> //.
  by apply row_length.
  by rewrite column_length=> //; smt.
  by apply row_get.
  by apply column_get=> //; smt.
  by apply transpose_get.
qed.
