(* Report Noisy Max *)

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

(* ---------------------------- Report Noisy Max --------------------------- *)

module M = {
  proc rnm(db : int list) : int = {
    var cur : int;
    var i : int;
    var output : int;
    var max : int;
    cur <- 0;
    i  <- 0;
    output <- -1;
    max <- 0;
    while (i < N) {
        cur <$ lap eps (evalQ i db);
        if (max < cur) {
          max <- cur; output <- i;
        }
        i <- i + 1;   
    }
    return output;
  }
}.
  
(* --------------------------------- Proof --------------------------------- *)

lemma rnm :
  aequiv [[eps & 0%r]
          M.rnm ~ M.rnm :
          adj db{1} db{2} ==> ={res}].
proof.
proc.
seq 4 4 :
  (adj db{1} db{2} /\ ={i, output, max, cur} /\
   i{1} = 0 /\ max{1} = 0 /\ cur{1} = 0). 
toequiv; auto.
pweq (output, output).
while true (N - i); auto; smt(lap_ll).
while true (N - i); auto; smt(lap_ll).
smt().
move => x.  (* output under consideration *)
(* tighten e to help in awhile *)
conseq
  <[(sumr N (fun (i : int) => if x = N - i - 1 then eps else 0%r)) &
    0%r]>.
move => &1 &2 /> _.
rewrite sum_le_most1_non0 //.
case (0 <= x < N) => [x_in_rng | x_not_in_rng].
right; exists (N - x - 1); smt(gt0_N).
left; smt().
awhile
  [(fun k => if x = N - k - 1 then eps else 0%r) & (fun _ => 0%r)]
  N [N - i - 1] 
  (adj db{1} db{2} /\ ={i, output} /\
   (max{1} < cur{1} => output{1} = i{1}) /\
   (max{2} < cur{2} => output{1} = i{1})).
smt(gt0_N).
smt(ge0_eps).
smt().
smt(gt0_N).
by rewrite /sumr sumr_const intmulr mul0r.
move => k.  (* in one-to-one-correspondence with program variable i,
               except ranges from N - 1 down instead of from 0 up *)
(* split into two cases *)
have cases : (x = N - k - 1) \/ (x <> N - k -1) by smt().
elim cases => [eq_x_N_min_k_min1 | ne_x_N_min_k_min1].
seq 1 1 : (* handle lap *)
  (adj db{1} db{2} /\ ={i, output} /\
   (max{1} < cur{1} => output{1} = i{1}) /\
   (max{2} < cur{2} => output{1} = i{1}) /\
   i{1} < N /\ k = N - i{1} - 1 /\ N - i{1} - 1 <= N /\
   ={cur})  (* NOTE - because first arg to lap is 0 *)
  <[(if x = N - k - 1 then eps else 0%r) & 0%r]>.
lap 0 1. smt(). smt(one_sens).
if{1}; if{2}; toequiv; auto; smt().
(* second case *)
(* bring evalQ i M.db in {1} and {2} into assumptions: *)
exists* (evalQ i db){1}; elim* => e1;
exists* (evalQ i db){2}; elim* => e2.
seq 1 1 : (* handle lap *)
  (e1 = evalQ i{1} db{1} /\ e2 = evalQ i{2} db{2} /\
   adj db{1} db{2} /\ ={i, output} /\
   (max{1} < cur{1} => output{1} = i{1}) /\
   (max{2} < cur{2} => output{1} = i{1}) /\
   i{1} < N /\ x <> N - k - 1 /\
   k = N - i{1} - 1 /\ N - i{1} - 1 <= N /\
   (* NOTE - because first arg to lap is (e2 - e1): *)
   cur{1} + (e2 - e1) = cur{2})  
  <[(if x = N - k - 1 then eps else 0%r) & 0%r]>.
lap (e2 - e1) 0; smt().
toequiv; auto; smt().
qed.
