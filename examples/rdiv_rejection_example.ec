(* ==========================================================================

   Worked example — Rényi hop from conditional to unconditional sampling.

   Setup
   -----
   A finite sample space [S] with a "bad" subset.  The adversary is
   given a single bit saying whether the sample is [good] (not bad) and
   must guess the sample.

   Real game: sample [s] *conditioned on being good* (rejection
   sampling), give the adversary the bit [!bad s] (always true), and
   check the guess.

   Ideal game: sample [s] *unconditionally*, give the adversary the bit
   [!bad s] (sometimes false), and check the guess.

   Both games give the adversary the same input shape.  The difference
   is in the sample distribution — and that difference matters,
   because the adversary's optimal strategy on [bad] inputs differs
   from its optimal strategy on [good] inputs.

   Why Rényi is needed
   -------------------
   Concretely: if [|S| = 2^256] and [|bad| = 2^10], then
   - [Pr[Adv wins | bad]  = 2^(-10)]     (guess uniformly from 2^10 bad
     strings — small space, high win rate).
   - [Pr[Adv wins | good] = 1/(2^256 - 2^10)]  (essentially [2^(-256)]).

   Real's win probability is [1/(2^256 - 2^10)] — adversary is stuck
   guessing in a huge space.

   Ideal's win probability is
     [(2^(-246)) * 2^(-10) + (1 - 2^(-246)) * 1/(2^256 - 2^10)] ≈
     [2^(-255)]
   — the [Pr[bad] * Pr[win|bad]] contribution *doubles* the probability.

   So [Real < Ideal], *not* equal.  The Rényi bound
     [Pr[Real wins] ≤ (1 / Pr[good]) · Pr[Ideal wins]]
   captures this with a factor that collapses to [≈ 1] here (since
   [good] has nearly full mass), giving [Real ≤ Ideal] up to a tiny
   correction — and *not* via distributional equality, which fails.

   Library pieces exercised
   ------------------------
   - [dominated_dcond] / [rdiv_inf_dcond]: per-query domination with
     the [1/Pr[good]] cost.
   - [adv_rdiv_inf_dcond]: pre-composed adversary-level bound.
   - No byequiv scaffolding is admitted — the reshape lemmas close
     cleanly via [byequiv; proc; inline; call; auto].

   ========================================================================== *)

require import AllCore Distr StdOrder StdRing RDiv.
(*---*) import RealOrder RField.

(* --- Abstract sample space ------------------------------------------ *)

type S.
op [lossless] dS : S distr.
op bad : S -> bool.
axiom good_pos : 0%r < mu dS (predC bad).

(* --- Adversary and games -------------------------------------------- *)

(* The adversary sees the good/bad bit and guesses the sample. *)
module type Adv = {
  proc guess(is_good : bool) : S
}.

(* Real: rejection-sample so [s] is always good. *)
module RealG(A : Adv) = {
  proc main() : bool = {
    var s, r;
    s <$ dcond dS (predC bad);
    r <@ A.guess(! bad s);
    return r = s;
  }
}.

(* Ideal: no rejection — the adversary may see [bad]. *)
module IdealG(A : Adv) = {
  proc main() : bool = {
    var s, r;
    s <$ dS;
    r <@ A.guess(! bad s);
    return r = s;
  }
}.

(* --- Reduction to the Distinguisher sampling game ------------------ *)

(* Clone the distinguisher theory at our sample type. *)
clone import RDiv.Distinguisher as D with
  type in_t <- S,
  type out_t <- bool
  proof*.

(* Adapter: wrap [A] into a [D.Dist].  The adapter receives the sample
   [s], derives the good/bad bit, calls [A.guess], and returns whether
   the guess matched. *)
module Reduction(A : Adv) : D.Dist = {
  proc guess(s : S) : bool = {
    var r;
    r <@ A.guess(! bad s);
    return r = s;
  }
}.

(* Reshape: Real is exactly [Sample(Reduction(A))] on [dcond dS good]. *)
lemma Real_Sample (A <: Adv) &m :
  Pr[RealG(A).main() @ &m : res] =
  Pr[D.Sample(Reduction(A)).main(dcond dS (predC bad)) @ &m : res].
proof.
byequiv => //; proc; inline *.
wp; call (: true); auto.
qed.

lemma Ideal_Sample (A <: Adv) &m :
  Pr[IdealG(A).main() @ &m : res] =
  Pr[D.Sample(Reduction(A)).main(dS) @ &m : res].
proof.
byequiv => //; proc; inline *.
wp; call (: true); auto.
qed.

(* --- Flagship: the Rényi hop --------------------------------------- *)

(* Real's win probability is bounded by [1/Pr[good]] times Ideal's.
   This is the whole cryptographic content of the hop — no
   distributional equality, just the Rényi-∞ factor. *)
lemma Real_Ideal_bound (A <: Adv) &m :
  Pr[RealG(A).main() @ &m : res] <=
    (1%r / mu dS (predC bad)) * Pr[IdealG(A).main() @ &m : res].
proof.
rewrite (Real_Sample A &m) (Ideal_Sample A &m).
exact (adv_rdiv_inf_dcond (Reduction(A)) (fun b => b) &m dS (predC bad) good_pos).
qed.

(* --- Sharpness discussion (comment only) --------------------------- *)

(* For [|S| = 2^256, |bad| = 2^10] and the uniform distribution on [S]:

     Pr[good] = 1 - 2^(-246)  ≈  1
     1/Pr[good] ≈ 1 + 2^(-246)

   So the Rényi factor is essentially 1.  The usefulness of the bound
   is that it holds for *any* adversary [A], including one that
   encodes knowledge of [bad] into its guessing strategy.

   For smaller sample spaces — or a more aggressive [bad] predicate —
   [Pr[good]] drops below [1/2] and the Rényi factor becomes a real
   quantitative cost.  That is where the bound does meaningful work.
*)
