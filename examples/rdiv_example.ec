(* ==========================================================================

   Worked example — RDiv applied to a concrete probability-preservation
   setup.

   Same scheme as [examples/sdist_example.ec]: sample [n] independent
   biased coin flips, count the heads, hand the count to an adversary.
   Here we state the Rényi-∞ variant: for any event on the adversary's
   output, its probability under [d1] is at most [(rdiv_inf d1 d2)^n]
   times its probability under [d2], provided [d1] is dominated by [d2].

   What this file demonstrates
   ---------------------------
   - The same concrete [module Summary] / [module Scheme] setup as the
     SDist example — so the reader can compare the two bounds.
   - A [module Reduction] adapting [Scheme] to [RDiv.DistinguisherList]'s
     [Sample] interface.
   - A [Scheme_Sample] equivalence lemma discharging the reshape step.
   - The flagship bound via [adv_rdiv_inf_dlist].

   ========================================================================== *)

require import AllCore List Distr DList StdOrder StdRing RDiv.
(*---*) import RealOrder RField.

op n : { int | 0 <= n } as ge0_n.

module Summary = {
  proc of_list (bs : bool list) : int = {
    var cnt;
    cnt <- size (filter (fun b => b) bs);
    return cnt;
  }
}.

module type Adv = {
  proc guess(cnt : int) : bool
}.

module Scheme(A : Adv) = {
  proc main(d : bool distr) = {
    var bs, cnt, r;
    bs  <$ dlist d n;
    cnt <@ Summary.of_list(bs);
    r   <@ A.guess(cnt);
    return r;
  }
}.

(* Clone the pre-composed [DistinguisherList] sub-theory at sample type
   [bool] and output type [bool].  This gives us [DL.Sample] and the
   fused [adv_rdiv_inf_dlist] lemma. *)
clone import RDiv.DistinguisherList as D with
  type t <- bool,
  type out_t <- bool
  proof*.

(* Reduction adapter — same shape as in the SDist example. *)
module Reduction(A : Adv) : DL.Dist = {
  proc guess(bs : bool list) = {
    var cnt, r;
    cnt <@ Summary.of_list(bs);
    r   <@ A.guess(cnt);
    return r;
  }
}.

lemma Scheme_Sample (A <: Adv) (P : bool -> bool) &m (d : bool distr) :
  Pr[Scheme(A).main(d) @ &m : P res] =
  Pr[DL.Sample(Reduction(A)).main(dlist d n) @ &m : P res].
proof.
byequiv => //; proc; inline *.
wp; call (: true); wp; rnd; auto.
qed.

(* Flagship bound: probability preservation on the concrete scheme.
   One-liner, modulo the reshape step above. *)
lemma adv_Scheme (A <: Adv) (P : bool -> bool) &m (d1 d2 : bool distr) :
  dominated d1 d2 =>
  Pr[Scheme(A).main(d1) @ &m : P res]
  <= exp (rdiv_inf d1 d2) n * Pr[Scheme(A).main(d2) @ &m : P res].
proof.
move => dom.
rewrite (Scheme_Sample A P &m d1) (Scheme_Sample A P &m d2).
exact (adv_rdiv_inf_dlist (Reduction(A)) P &m d1 d2 n ge0_n dom).
qed.
