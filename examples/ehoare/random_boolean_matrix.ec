require import AllCore Array Real RealExp List.
(*---*) import RField.
require import Distr DBool Xreal.
(*---*) import Biased.
require import StdOrder.
(*---*) import RealOrder.

(* uniformly sampling a 2-d boolean array of size n x m *)
module M = {
  proc sample (n : int, m : int, a : bool array) : (bool array) = {
    var i, j : int;
    var b : bool;
    i <- 0;
    while (i < n) {
      j <- 0;
      while (j < m) {
        b <$ dbiased 0.5;
        a.[i * m + j] <- b;
        j <- j + 1;
      }
      i <- i + 1;
    }
    return a;
  }
}.

op row_eq_upto (i m : int) (a1 a2 : bool array) =
  forall (i' j' : int),
     0 <= i' < i
  => 0 <= j' < m
  => a1.[i' * m + j'] = a2.[i' * m + j'].

op cell_eq_upto (i j m : int) (a1 a2 : bool array) =
  forall (j' : int),
     0 <= j' < j
  => a1.[i * m + j'] = a2.[i * m + j'].

lemma row_eq_upto_increase (i m : int) (a1 a2 : bool array):
      0 <= i
   => (row_eq_upto i m a1 a2 /\ cell_eq_upto i m m a1 a2
   <=> row_eq_upto (i + 1) m a1 a2).
proof.
move => ? @/row_eq_upto @/cell_eq_upto; split.
- move => ? i' j' ??.
  by case: (i' < i) => /#.
- move => H; split.
  - move => i' j' ??.
    have ?: 0 <= i' < i + 1 by smt().
    by have := H i' j' _ _.
  - by have := H i => /#.
qed.

lemma cell_eq_upto_false (i j' j m : int) (a1 a2 : bool array) :
     0 <= j' < j
  => a1.[i * m + j'] <> a2.[i * m + j']
  => cell_eq_upto i j m a1 a2 = false.
proof. by smt(). qed.

lemma cell_eq_upto_split (i j m : int) (a1 a2 : bool array) :
     0 <= j < m
  => (cell_eq_upto i (j + 1) m a1 a2
         <=> (cell_eq_upto i j m a1 a2
              /\ a1.[i * m + j] = a2.[i * m + j])
     ).
proof.
move => ? @/cell_eq_upto; split.
- move => H; split.
  - move => j' ?.
    have ?: 0 <= j' < j + 1 by smt().
    by have := H j' _.
  - by smt().
- move => ? j' ?.
  by case (j' < j) => /#.
qed.

lemma row_eq_upto_unrelated_set (i m x : int) (v : bool) (a1 a2 : bool array):
     i * m <= x < size a1
  => (row_eq_upto i m a1 a2 <=> row_eq_upto i m a1.[x <- v] a2).
proof.
move => ? @/row_eq_upto; split.
- move => ? i' j' ??.
  rewrite get_set 1:/#.
  have -> /=: !(i' * m + j' = x) by smt().
  by smt().
- move => ? i' j' ??.
  by rewrite (_: a1.[_] = a1.[x <- v].[i' * m + j']) 1:get_set /#.
qed.

lemma cell_eq_upto_unrelated_set (i j m x : int) (v : bool) (a1 a2 : bool array) :
     0 <= i /\ 0 <= j < m /\ i * m + j <= x < size a1
  => (cell_eq_upto i j m a1 a2 <=> cell_eq_upto i j m a1.[x <- v] a2).
proof.
move => [#] ????? @/cell_eq_upto; split.
- move => ? j' ?.
  rewrite get_set 1:/#.
  have -> /=: !(i * m + j' = x) by smt().
  by smt().
- move => ? j' ?.
  by rewrite (_: a1.[_] = a1.[x <- v].[i * m + j']) 1:get_set /#.
qed.

(* The probability of every possible boolean matrix of size n x m is no more than 2 ^ -(n * m) *)
lemma L:
  forall (a0 : bool array),
    ehoare [M.sample :
            (0 <= arg.`1
          /\ 0 <= arg.`2
          /\ size arg.`3 = arg.`1 * arg.`2
          /\ size arg.`3 = size a0)
        `|` (1%r / (2%r ^ (n * m)))%xr ==> (res = a0)%xr].
proof.
move => a0.
proc.
while ((0 <= i <= n
     /\ 0 <= m
     /\ size a = n * m
     /\ size a0 = size a)
   `|`  (2%r ^ ((-(n - i) * m)%r))%xr
       * (row_eq_upto i m a a0)%xr).
(* !cond => inv => pos_f <= inv_f *)
+ move => &hr.
  apply xle_cxr_r => ?.
  apply xle_cxr_r => ?.
  have ->: n{hr} - i{hr} = 0 by smt().
  rewrite Ring.IntID.mul0r Ring.IntID.oppr0 rpow0 mul1m_simpl.
  apply xle_rle; split => *; 1: by smt().
  exact le_b2r.
(* {cond /\ inv | inv_f} c {inv | inv_f} *)
+ wp.
  while (( 0 <= i < n
        /\ 0 <= j <= m
        /\ size a = n * m
        /\ size a = size a0)
          `|` (2%r ^ ((-((n - i) * m - j))%r))%xr
            * (row_eq_upto i m a a0 /\ cell_eq_upto i j m a a0)%xr).
  (* !cond => inv => pos_f <= inv_f *)
  + move => &hr />.
    rewrite xle_cxr_r => ?.
    rewrite xle_cxr_l 1:/#.
    rewrite (_: - _ * m{hr} = - ((n{hr} - i{hr}) * m{hr} - j{hr})) //= 1:/#.
    rewrite (_: j{hr} = m{hr}) 1:/#.
    by rewrite -row_eq_upto_increase 1:/# ler_eqVlt; left; reflexivity.
  (* {cond /\ inv | inv_f} c {inv | inv_f} *)
  + wp; skip => /> &hr.
    rewrite xle_cxr_r => [#] 5? Hsize ?.
    rewrite Ep_dbiased /= 1:/#.
    have -> /=: 0 <= i{hr} < n{hr} by smt().
    have -> /=: 0 <= j{hr} + 1 <= m{hr} by smt().
    rewrite !size_set !Hsize /=.
    have -> /=: n{hr} * m{hr} = size a0 by smt().
    rewrite !to_pos_pos 1,2,3,4,5:#smt:(rpow_gt0 b2r_ge0).
    rewrite !cell_eq_upto_split 1,2:/# !get_set //=.
    - split; 1: by smt().
      move => ?.
      by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
    - split; 1: by smt().
      move => ?.
      by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
    case (a0.[i{hr} * m{hr} + j{hr}]) => Hcase /=.
    + rewrite -row_eq_upto_unrelated_set.
      - split; 1: by smt().
        move => ?.
        by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
      rewrite -cell_eq_upto_unrelated_set.
      - do! split; 1,2,3: by smt().
        move => ?.
        by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
      rewrite -{2}(rpow1 2%r) // -rpowN // -mulrA.
      rewrite (mulrC (b2r _) (2%r ^ - 1%r)).
      by rewrite mulrA -rpowD // /#.
    + rewrite /= -row_eq_upto_unrelated_set.
      - split; 1: by smt().
        move => ?.
        by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
      rewrite -cell_eq_upto_unrelated_set.
      - do! split; 1,2,3: by smt().
        move => ?.
        by apply (IntOrder.ltr_le_trans ((n{hr} - 1) * m{hr} + m{hr})) => /#.
      rewrite -{2}(rpow1 2%r) // -rpowN // -mulrA.
      rewrite (mulrC (b2r _) (2%r ^ - 1%r)).
      by rewrite mulrA -rpowD // /#.
  (* pre => inv *)
  + wp; skip => &hr />.
    rewrite xle_cxr_r => [#] ??????.
    rewrite xle_cxr_l 1:/#.
    by have-> //: cell_eq_upto i{hr} 0 m{hr} a{hr} a0 by smt().
auto => /> &hr.
rewrite xle_cxr_r => [#] ????.
rewrite xle_cxr_l 1:/# fromintN rpowN //= rpow_int //=.
by have ->: row_eq_upto 0 m{hr} a{hr} a0 by smt().
qed.
