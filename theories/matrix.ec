require import pair.
require import int.
require        array.

(* We could use the type of arrays, but would then require a validity condition *)
type 'a matrix.

op size: 'a matrix -> (int * int).

axiom size_pos: forall (M:'a matrix),
  0 <= fst (size M) /\ 0 <= snd (size M).

op __get: ('a matrix,(int * int)) -> 'a.

pred [==] (M0 M1:'a matrix) =
  size M0 = size M1 /\
  forall (i j:int),
    0 <= i => i < fst (size M0) =>
    0 <= j => j < snd (size M0) =>
    M0.[(i,j)] = M1.[(i,j)].

axiom extentionality: forall (M0 M1:'a matrix),
  M0 == M1 => M0 = M1.

op new: (int * int) -> 'a matrix.

axiom new_size: forall m n,
  size (new<:'a> (m,n)) = (m,n).

op __set: ('a matrix,(int * int),'a) -> 'a matrix.

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