(* Differential Privacy of Above Threshold *)

prover quorum=2 ["Alt-Ergo" "Z3"].

require import AllCore.
require import Distr List Aprhl StdRing StdOrder StdBigop.
(*---*) import IntOrder RField RealOrder.

(* ------------------------------- Parameters ------------------------------ *)

op eps : { real | 0%r <= eps } as ge0_eps.  (* epsilon *)
hint exact : ge0_eps.

op N : { int | 0 < N } as gt0_N.  (* number of iterations *)
hint exact : gt0_N.

op T : { int | 0 < T } as gt0_T.  (* threshold *)
hint exact : gt0_N.

pred adj : int list & int list.  (* adjacency *)

op evalQ : int -> int list -> int.  (* query evaluation *)

axiom one_sens d1 d2 i :  (* sensitivity *)
  adj d1 d2 => `|evalQ i d1 - evalQ i d2| <= 1.

(* ----------------------------- Helper Lemmas ----------------------------- *)

lemma sumr0 (n : int) :
  0 <= n => sumr n (fun (_ : int) => 0%r) = 0%r.
proof.
move => ge0_n.
rewrite /sumr sumri_const 1:ge0_n 1:intmulr /#.
qed.

lemma sum_le_most1_non0 (r : real, f : int -> real, N : int) :
  0%r <= r => 0 < N =>
  (forall (i : int), 0 <= i < N => f i = 0%r) \/
  (exists (i : int),
   0 <= i < N /\ f i = r /\
   (forall (j : int), 0 <= j < N => j <> i => f j = 0%r)) =>
  sumr N f <= r.
proof.
rewrite /sumr => ge0_r gt0_N [all0 | [i] [#] ge0_i lt_i_N f_i_eq_r f_non_i].
rewrite (eq_big_int 0 N f (fun i => 0%r)) 1:/#.
by rewrite -/(sumr N (fun (_ : int) => 0%r)) sumr0 1:ltzW 1:gt0_N.
rewrite (big_cat_int i) // 1:/#.
have -> : bigi predT f 0 i = 0%r.
  rewrite (eq_big_int 0 i f (fun i => 0%r)) 1:/#.
  rewrite -/(sumr i (fun i => 0%r)) sumr0 /#.
rewrite -(add0r r) ler_add2l big_ltn // f_i_eq_r -{2}(addr0 r).
rewrite ler_add2l lerr_eq (eq_big_int (i + 1) N f (fun i => 0%r)) 1:/#.
by rewrite sumri_const 1:/# intmulr.
qed.

(* ----------------------- Above Threshold Algorithm ----------------------- *)

module M = {
  proc aboveT (db : int list) : int = {
    var i : int;
    var nT : int;
    var cur : int;
    var output: int;
    cur <- 0;
    i <- 0;
    output <- N;
    (* noisy threshold*)
    nT <$ lap (eps/2%r) T;
    while (i < N) {
      cur <$ lap (eps/4%r) (evalQ i db);
      if (nT <= cur /\ output = N) {
        output <- i;
      }
      i <- i + 1;
    }
    return output;
  }
}.

(* --------------------------------- Proof --------------------------------- *)

lemma aboveT :
  aequiv [[eps & 0%r]
          M.aboveT ~ M.aboveT :
          (adj db{1} db{2}) ==> ={res}].
proof.
proc.
seq 3 3 :
  (adj db{1} db{2} /\ ={output, i, cur} /\ output{1} = N /\
   i{1} = 0 /\ cur{1} = 0).
toequiv; auto. 
seq 1 1 :
  (adj db{1} db{2} /\ ={output, i, cur} /\
   output{1} = N /\ i{1} = 0 /\ nT{1} + 1 = nT{2})
  <[(eps / 2%r) & 0%r]>.  (* spend first half of budget *)
lap 1 1.
pweq (output, output).
while true (N - i); auto; smt(lap_ll).
while true (N - i); auto; smt(lap_ll).
smt(). 
move => R.  (* output under consideration *)
(* tighten e to help in awhile *)
conseq
  <[(sumr N (fun i => if R = N - i - 1 then eps / 2%r else 0%r)) &
    0%r]>.
move => &1 &2 /> _.
have -> : eps - eps / 2%r = eps/2%r by smt().
rewrite sum_le_most1_non0 //.
smt(ge0_eps).
case (0 <= R < N) => [R_in_rng | R_not_in_rng].
right; exists (N - R - 1); smt(gt0_N).
left; smt().
awhile
  [(fun k => if R = N - k - 1 then eps / 2%r else 0%r) &
   (fun _ => 0%r)]
  N [N - i - 1] 
  (adj db{1} db{2} /\ ={i} /\ 0 <= i{1} <= N /\ nT{1} + 1 = nT{2} /\ 
   (N = output{1} => N = output{2}) /\
   (R = output{1} => R = output{2}) /\
   (i{1} < R => output{1} = N \/ output{1} < R)).
smt(gt0_N).
smt(ge0_eps).
smt().
smt(gt0_N).
by rewrite /sumr sumr_const intmulr mul0r.
move => k.  (* in one-to-one-correspondence with program variable i,
               except ranges from N - 1 down instead of from 0 up *)
(* split into two cases *)
have cases : R =  N - k - 1 \/ R <> N - k - 1 by smt().
elim cases => [eq_R_N_min_k_min1 | ne_R_N_min_k_min1].
(* first case: R = N - k - 1 *)
(* simplify e *)
conseq <[(eps / 2%r) & 0%r]>; first smt().
seq 1 1 :
  (adj db{1} db{2} /\ nT{1} + 1 = nT{2} /\
   ={i} /\ 0 <= i{1} < N /\ k = N - i{1} - 1 /\ R = i{1} /\
   (R = output{1} => R = output{2}) /\
   (N = output{1} => N = output{2}) /\ 
   cur{1} + 1 = cur{2})   (* NOTE *)
  <[(eps / 2%r) & 0%r]>.  (* spend second half of budget *)
lap 1 2.
smt().
progress.
rewrite (lez_trans (`|1| + `|evalQ i{2} db{1} - evalQ i{2} db{2}|))
        1:lez_norm_add.
smt(one_sens).
smt().
toequiv; auto; smt().
(* second case: R <> N - k - 1 *)
(* simplify e *)
conseq <[0%r & 0%r]>; first smt().
exists* (evalQ i db){1}; elim* => e1.  (* so can use in arg to lap *)
exists* (evalQ i db){2}; elim* => e2.
seq 1 1:
  (adj db{1} db{2} /\ nT{1} + 1 = nT{2} /\
   ={i} /\ 0 <= i{1} < N  /\ k = N - i{1} - 1 /\
   (N = output{1} => N = output{2}) /\
   (R = output{1} => R = output{2}) /\
   (i{1} < R => output{1} = N \/ output{1} < R) /\
   cur{2} <= cur{1} + 1).  (* NOTE *)
lap (e2 - e1) 0.
smt().
progress.
by rewrite ler_add2l 1:(lez_trans (`|evalQ i{2} db{2} - evalQ i{2} db{1}|))
           1:ler_norm 1:distrC 1:one_sens.
toequiv; auto; smt().
qed.
