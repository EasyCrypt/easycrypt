(* GlobalHybrid.ec *)

(*^ This theory proves several lemmas about __global__ hybrids,
    hybrids whose entire behavior, not just that of any oracles they
    may use, can be a function of the hybrid index `i`.

    We have a lemma based on the triangular inequality, where the
    overall upper bound is the sum of the bounds of the individual
    steps, as well as the specialization of this to the case where
    each step's bound is the same.

    And we have a lemma for hybrids parameterized by an oracle
    that gives an equality, not just an upper bound, assuming
    a natural precondition holds. This lemma is adapted
    from the Nominal-SSProve paper "Mechanizing Nested Hybrid Arguments",
    https://eprint.iacr.org/2025/1122 ^*)

require import AllCore Real StdOrder StdBigop Distr.
import RealOrder Bigreal BRA.
require TotalProb.

(*& Type of additional input. &*)

type input.

(*& Module type of global hybrids. &*)

module type HYBRID = {
  (* i is the index of the hybrid, starting from 1
     x is an additional input *)
  proc main(x : input, i : int) : bool
}.

(*& General global hybrid lemma; the bound for each step is a function
    of the index. &*)

lemma hybrid_gen (x : input) (n : int) (p : int -> real) (M <: HYBRID) &m :
  1 <= n =>
  (forall (i : int),
   1 <= i < n =>
   `|Pr[M.main(x, i) @ &m : res] - Pr[M.main(x, i + 1) @ &m : res]| <= p i) =>
  `|Pr[M.main(x, 1) @ &m : res] - Pr[M.main(x, n) @ &m : res]| <=
  bigi predT p 1 n.
proof.
move => ge1_n step.
have ind :
  forall (i : int),
  0 <= i => 1 <= i <= n =>
  `|Pr[M.main(x, 1) @ &m : res] -
    Pr[M.main(x, i) @ &m : res]| <= bigi predT p 1 i.
+ elim => [// | i ge0_i IH [_ i_plus1_le_n]].
  case (i = 0) => [-> /= |].
  + by rewrite ger0_norm // big_geq.
  rewrite -lt0n // ltzE /= => ge1_i.
  rewrite big_int_recr //.
  rewrite (ler_trans
           (`|Pr[M.main(x, 1) @ &m : res] -
              Pr[M.main(x, i) @ &m : res]| +
            `|Pr[M.main(x, i) @ &m : res] -
              Pr[M.main(x, i + 1) @ &m : res]|)).
  + by rewrite RealOrder.ler_dist_add.
  by rewrite ler_add 1:IH 1:/# step /#.
by rewrite ind // (IntOrder.ler_trans 1).
qed.

(*& Simple global hybrid lemma; the bound for each step is a constant. &*)

lemma hybrid_simp (x : input) (n : int) (p : real) (M <: HYBRID) &m :
  1 <= n =>
  (forall (i : int),
   1 <= i < n =>
   `|Pr[M.main(x, i) @ &m : res] -
     Pr[M.main(x, i + 1) @ &m : res]| <= p) =>
  `|Pr[M.main(x, 1) @ &m : res] -
    Pr[M.main(x, n) @ &m : res]| <= (n - 1)%r * p.
proof.
move => ge1_n step.
have HG := hybrid_gen x n (fun _ => p) M &m _ _ => //.
by rewrite Bigreal.sumri_const in HG.
qed.

(*& Hybrids parameterized by an oracle. &*)

theory Param.

clone TotalProb.TotalRange as TR with
  type input <- input
proof *.

(*& Types of oracle inputs. &*)

type or_input.

(*& Types of oracle outputs. &*)

type or_output.

(*& Oracle module type. &*)

module type OR = {
  proc init() : unit
  proc f(x : or_input) : or_output
}.

(*& Parameterized hybrid module type. &*)

module type HYBRID_PARAM (Or : OR) = {
  (* i is the index of the hybrid, starting from 1
     x is an additional input *)
  proc main(x : input, i : int) : bool {Or.f}
}.

(*& Parameterized hybrid experiment. &*)

module Exper(M : HYBRID_PARAM, Or : OR) = {
  proc main(x : input, i : int) : bool = {
    var b : bool;
    Or.init();
    b <@ M(Or).main(x, i);
    return b;
  }
}.

(*& Parameterized hybrid lemma. &*)

lemma hybrid_param (x : input) (n : int) (Or1 <: OR) (Or2 <: OR)
                   (M <: HYBRID_PARAM) &m :
  1 < n =>
  (forall (i : int),
   1 <= i < n =>
   Pr[Exper(M, Or2).main(x, i) @ &m : res] =
   Pr[Exper(M, Or1).main(x, i + 1) @ &m : res]) =>
  `|Pr[Exper(M, Or1).main(x, 1) @ &m : res] -
    Pr[Exper(M, Or1).main(x, n) @ &m : res]| =  (* also Or1 *)
  (n - 1)%r *
  `|Pr[TR.Rand(Exper(M, Or1)).f(drange 1 n, x) @ &m : res] -
    Pr[TR.Rand(Exper(M, Or2)).f(drange 1 n, x) @ &m : res]|.
proof.
move => gt1_n steps.
rewrite
  (telescoping_sum
   (fun i => Pr[Exper(M, Or1).main(x, i) @ &m : res])) 1:/# /=.
rewrite
  (eq_big_int _ _ _
   (fun (i : int) =>
      Pr[Exper(M, Or1).main(x, i) @ &m : res] -
      Pr[Exper(M, Or2).main(x, i) @ &m : res]) _).
+ by move => i i_rng /=; rewrite -steps.
rewrite big_split -sumrN.
rewrite (TR.total_prob_drange (Exper(M, Or1))) //.
rewrite (TR.total_prob_drange (Exper(M, Or2))) //.
rewrite -normrZ 1:/# RField.mulrC RField.mulrBl 2!mulr_suml /=.
have -> :
  (fun (i : int) =>
     Pr[Exper(M, Or1).main(x, i) @ &m : res] * (n - 1)%r / (n - 1)%r) =
  (fun (i : int) => Pr[Exper(M, Or1).main(x, i) @ &m : res]).
+ by apply fun_ext => i; rewrite -RField.mulrA Num.Domain.divrr /#.
have -> :
  (fun (i : int) =>
     Pr[Exper(M, Or2).main(x, i) @ &m : res] * (n - 1)%r / (n - 1)%r) =
  (fun (i : int) => Pr[Exper(M, Or2).main(x, i) @ &m : res]).
+ by apply fun_ext => i; rewrite -RField.mulrA Num.Domain.divrr /#.
done.
qed.

(*& Lemma for understanding the result. &*)

lemma hybrid_param_result (x : input) (n : int)
                          (M1 <: TR.T) (M2 <: TR.T) &m :
  1 < n =>
  (n - 1)%r *
  `|Pr[TR.Rand(M1).f(drange 1 n, x) @ &m : res] -
    Pr[TR.Rand(M2).f(drange 1 n, x) @ &m : res]| =
  `|bigi predT
    (fun (i : int) =>
       Pr[M1.main(x, i) @ &m : res] -
       Pr[M2.main(x, i) @ &m : res])
    1 n|.
proof.
move => gt1_n.
rewrite (TR.total_prob_drange M1) //.
rewrite (TR.total_prob_drange M2) //.
rewrite -normrZ 1:/# RField.mulrC RField.mulrBl 2!mulr_suml /=.
have -> :
  (fun (i : int) =>
     Pr[M1.main(x, i) @ &m : res] * (n - 1)%r / (n - 1)%r) =
  (fun (i : int) => Pr[M1.main(x, i) @ &m : res]).
+ by apply fun_ext => i; rewrite -RField.mulrA Num.Domain.divrr /#.
have -> :
  (fun (i : int) =>
     Pr[M2.main(x, i) @ &m : res] * (n - 1)%r / (n - 1)%r) =
  (fun (i : int) => Pr[M2.main(x, i) @ &m : res]).
+ by apply fun_ext => i; rewrite -RField.mulrA Num.Domain.divrr /#.
by rewrite
     (sumrB predT
      (fun (i : int) => Pr[M1.main(x, i) @ &m : res])
      (fun (i : int) => Pr[M2.main(x, i) @ &m : res])).
qed.

end Param.
