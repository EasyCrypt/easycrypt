(* GlobalHybrid.ec *)

(*^ Consider a module `M` with a `bool`-returning procedure `main`
    taking an integer `i` as its argument. We consider the result of
    calling `M` with argument `i`, where `i` is in the range `1 .. n`
    inclusive, for `n >= 1`, to be the `i`th __global hybrid__,
    global because its entire behavior, and not just that of an oracle
    it may use, can be a function of `i`.

    This theory provides lemmas for upper bounding the absolute value
    of the difference of the probabilities of the first and last
    hybrids returning true, given upper bounds on the absolute values
    of the probability differences for each of the steps, as a function
    of `i`.
^*)

require import AllCore Real StdOrder StdBigop.
import RealOrder Bigreal BRA.

(*& Module type of global hybrids. &*)

module type HYBRID = {
  (* i is the index of the hybrid, starting from 1 *)
  proc main(i : int) : bool
}.

(*& General global hybrid lemma; the bound for each step is a function
    of the index. &*)

lemma hybrid_gen (n : int) (p : int -> real) (M <: HYBRID) &m :
  1 <= n =>
  (forall (i : int),
   1 <= i < n => 
   `|Pr[M.main(i) @ &m : res] - Pr[M.main(i + 1) @ &m : res]| <= p i) =>
  `|Pr[M.main(1) @ &m : res] - Pr[M.main(n) @ &m : res]| <=
  bigi predT p 1 n.
proof.
move => ge1_n step.
have ind :
  forall (i : int),
  0 <= i => 1 <= i <= n =>
  `|Pr[M.main(1) @ &m : res] - Pr[M.main(i) @ &m : res]| <= bigi predT p 1 i.
  elim => [// | i ge0_i IH [_ i_plus1_le_n]].
  case (i = 0) => [-> /= |].
  by rewrite ger0_norm // big_geq.
  rewrite -lt0n // ltzE /= => ge1_i.
  rewrite big_int_recr //.
  rewrite (ler_trans
           (`|Pr[M.main(1) @ &m : res] - Pr[M.main(i) @ &m : res]| +
            `|Pr[M.main(i) @ &m : res] - Pr[M.main(i + 1) @ &m : res]|)).
  rewrite RealOrder.ler_dist_add.
  rewrite ler_add 1:IH 1:/# step /#.
by rewrite ind // (IntOrder.ler_trans 1).
qed.

(*& Simple global hybrid lemma; the bound for each step is a constant. &*)

lemma hybrid_simp (n : int) (p : real) (M <: HYBRID) &m :
  1 <= n =>
  (forall (i : int),
   1 <= i < n => 
   `|Pr[M.main(i) @ &m : res] - Pr[M.main(i + 1) @ &m : res]| <= p) =>
  `|Pr[M.main(1) @ &m : res] - Pr[M.main(n) @ &m : res]| <= (n - 1)%r * p.
proof.
move => ge1_n step.
have HG := hybrid_gen n (fun _ => p) M &m _ _ => //.
by rewrite Bigreal.sumri_const in HG.
qed.
