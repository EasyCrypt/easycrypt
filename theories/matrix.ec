require import pair.
require import int.

(* Type declaration and core definitions *)
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

(* Operators *)
(* new (m,n): allocates a new uninitialized (m,n) matrix *)
op new: (int * int) -> 'a matrix.

axiom new_size: forall m n,
  0 <= m => 0 <= n =>
  size (new<:'a> (m,n)) = (m,n).

(* set M (i,j) a: M.[(i,j) <- a] whenever (i,j) < size M [pairwise] *)
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

(* sub M (i,j) (m,n): extracts the sub matrix of size (m,n) starting at (i,j) [whenever sizes fit] *)
op sub: ('a matrix,(int * int),(int * int)) -> 'a matrix.

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
op write: ('a matrix,(int * int),'a matrix,(int * int),(int * int)) -> 'a matrix.

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
  sub (write M (i,j) M' (0,0) (size M')) (i,j) (size M') = M'
proof.
intros M M' i j i_0 i_bound j_0 j_bound.
apply extentionality<:'a> ((sub (write M (i,j) M' (0,0) (size M')) (i,j) (size M')),M',_).
trivial.
save.

(* transpose M *)
op transpose: 'a matrix -> 'a matrix.

axiom transpose_size: forall (M:'a matrix),
  size (transpose M) = let (m,n) = size M in (n,m).

axiom transpose_get: forall (M:'a matrix) i j,
  0 <= i => i < snd (size M) =>
  0 <= j => j < fst (size M) =>
  (transpose M).[(i,j)] = M.[(j,i)].

lemma transpose_idempotent: forall (M:'a matrix),
  transpose (transpose M) = M
proof.
intros M.
apply extentionality<:'a> ((transpose (transpose M)),M,_).
trivial.
save.

(* Interactions with arrays *)
require array.

(* Casting a one-row matrix to array *)
op to_array: 'a matrix -> 'a array.array.

axiom to_array_length: forall (M:'a matrix),
  fst (size M) = 1 =>
  array.length (to_array M) = snd (size M).

axiom to_array_get: forall (M:'a matrix) i,
  fst (size M) = 1 =>
  0 <= i => i < snd (size M) =>
  array.__get (to_array M) i = M.[(i,0)].

(* Extracting a row *)
op row: ('a matrix,int) -> 'a array.array.

axiom row_length: forall (M:'a matrix) j,
  0 <= j => j < snd (size M) =>
  array.length (row M j) = fst (size M).

axiom row_get: forall (M:'a matrix) j i,
  0 <= j => j < snd (size M) =>
  0 <= i => i < fst (size M) =>
  array.__get (row M j) i = M.[(i,j)].

(* Extracting a column *)
op column: ('a matrix,int) -> 'a array.array.

axiom column_length: forall (M:'a matrix) i,
  0 <= i => i < fst (size M) =>
  array.length (column M i) = snd (size M).

axiom column_get: forall (M:'a matrix) i j,
  0 <= i => i < fst (size M) =>
  0 <= j => j < snd (size M) =>
  array.__get (column M i) j = M.[(i,j)].

lemma column_transpose_row: forall (M:'a matrix) i,
  0 <= i => i < snd (size M) =>
  row M i = column (transpose M) i
proof.
intros M i i_0 i_bound.
apply array.extentionality<:'a> ((row M i),(column (transpose M) i),_).
  cut ext_eq: (array.length (row M i) = fst (size M) /\
               array.length (column (transpose M) i) = fst (size M) /\
               forall j, 0 <= j => j < fst (size M) =>
                 array.__get (row M i) j = array.__get (column (transpose M) i) j);trivial.
save.