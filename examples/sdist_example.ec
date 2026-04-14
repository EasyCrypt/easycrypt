(* ==========================================================================

   Worked example — SDist applied to a concrete distinguishing game.

   The scheme samples [n] independent biased coin flips, publishes a
   single-integer summary (the count of heads), and lets an adversary
   guess a bit from that summary.  We bound the advantage of any such
   adversary between two coin distributions by [n * sdist d1 d2].

   What this file demonstrates
   ---------------------------
   - A concrete [module Summary] with real code doing the post-processing.
   - A user-facing [module Scheme] that combines [dlist] sampling,
     post-processing, and an abstract adversary.
   - A [module Reduction] that adapts [Scheme] into the form expected by
     [SDist.Dist.Sample] — this is the "reshape step" users always have
     to do before citing [adv_sdist].
   - An equivalence lemma [Scheme_Sample] discharging the reshape.
   - The final bound [adv_Scheme] via [adv_sdist] + [sdist_dlist].

   ========================================================================== *)

require import AllCore List Distr DList StdOrder SDist.
(*---*) import RealOrder.

(* Number of coin flips sampled by the scheme.  Fixed as an [op] to keep
   the Scheme interface minimal (one [distr] argument). *)
op n : { int | 0 <= n } as ge0_n.

(* Concrete post-processing: count the [true] values in a bool list.
   This is real code, not an abstract specification — the module body
   compiles to an actual [proc]. *)
module Summary = {
  proc of_list (bs : bool list) : int = {
    var cnt;
    cnt <- size (filter (fun b => b) bs);
    return cnt;
  }
}.

(* The adversary sees the count and returns a guess bit. *)
module type Adv = {
  proc guess(cnt : int) : bool
}.

(* User-facing scheme: sample coins, summarise, hand to the adversary. *)
module Scheme(A : Adv) = {
  proc main(d : bool distr) = {
    var bs, cnt, r;
    bs  <$ dlist d n;
    cnt <@ Summary.of_list(bs);
    r   <@ A.guess(cnt);
    return r;
  }
}.

(* Reshape the game into [Sample]-form.  Clone [SDist.Dist] at the sample
   type [bool list]; the cloned theory provides [Distinguisher] and
   [Sample]. *)
clone import SDist.Dist as D with
  type a <- bool list
  proof*.

import D.GenDist.

(* Adapter: wraps [A] so that the combined module is a
   [D.Distinguisher].  The wrapper does the post-processing inline. *)
module Reduction(A : Adv) : Distinguisher = {
  proc guess(bs : bool list) = {
    var cnt, r;
    cnt <@ Summary.of_list(bs);
    r   <@ A.guess(cnt);
    return r;
  }
}.

(* The reshape is exact: running [Scheme] equals running [Sample] on the
   pre-sampled list.  Any event on [res] is preserved. *)
lemma Scheme_Sample (A <: Adv) (P : bool -> bool) &m (d : bool distr) :
  Pr[Scheme(A).main(d) @ &m : P res] =
  Pr[Sample(Reduction(A)).main(dlist d n) @ &m : P res].
proof.
byequiv => //; proc; inline *.
wp; call (: true); wp; rnd; auto.
qed.

(* Flagship bound: advantage is linear in [n] and in [sdist]. *)
lemma adv_Scheme (A <: Adv) &m (d1 d2 : bool distr) :
  `| Pr[Scheme(A).main(d1) @ &m : res]
     - Pr[Scheme(A).main(d2) @ &m : res] |
  <= n%r * sdist d1 d2.
proof.
rewrite (Scheme_Sample A (fun b => b) &m d1).
rewrite (Scheme_Sample A (fun b => b) &m d2).
apply (ler_trans (sdist (dlist d1 n) (dlist d2 n))).
- exact (adv_sdist (Reduction(A))).
exact/sdist_dlist/ge0_n.
qed.
