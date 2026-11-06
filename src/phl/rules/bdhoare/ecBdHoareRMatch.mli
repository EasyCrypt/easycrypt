(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_rmatch_framed = {
  brmf_at   : nm_codepos1;   (* position k of the match (resolved) *)
  brmf_ctor : int;           (* index j of the constructor C *)
}

(* [t_bdhoare_rmatch_framed { brmf_at = k; brmf_ctor = j }] — framed form
   of [match C k]. With [c = hd; i; tl], [hd = c[0..k)] and
   [i = c[k] = match e with ... | C xs => b | ...], [C] its [j]-th
   constructor, and [~] the goal's comparison:

       hoare [hd : P ==> exists xs, e = C xs]
       phoare [hd; b[ys/xs]; tl : e = C ys /\ P ==> Q] ~ d
     -----------------------------------------------------  e indep. of hd,
                  phoare [c : P ==> Q] ~ d                  ~ is <= or hd = []

   where [ys] are fresh program variables, added to the memory of the
   second premise. Side conditions: [i] is a [match] with a [j]-th
   constructor; the variables read by [e] are neither read nor written by
   [hd]; [~] is [<=] or [hd] is empty.

   This is not a program transformation: [e = C ys] goes to the
   precondition, so the rule is stated on the whole statement (implicit
   seq around the match). It is retained as a separate rule pending a
   later discussion (the unframed form of [match C k] is the program
   transformation [EcTrRMatch]). It is sound because [e] has the same
   value before and after [hd], and because, in an initial memory in which
   [hd] does not terminate, the probability of [Q] is 0, below any upper
   bound: in the other ones, the first premise yields [ys] with
   [e = C ys] initially. For [=] and [>=], such a memory is not covered by
   the second premise, hence the restriction to an empty prefix.

   Node: [RBdHoareRMatchFramed { brmf_at = k; brmf_ctor = j }].
   Checker: "bdhoare-rmatch-framed" (it re-checks the side conditions). *)
val t_bdhoare_rmatch_framed : bdhoare_rmatch_framed -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

type bdhoare_rmatch_rule = {
  brmr_at   : codepos1;   (* position k of the match *)
  brmr_ctor : symbol;     (* constructor C of the branch taken *)
}

(* [t_bdhoare_rmatch { brmr_at = k; brmr_ctor = C }] — decides the match
   [i = c[k]] of [phoare [c : P ==> Q] ~ d] in favour of its [C] branch.
   Resolves [k] to an index and [C] to its index [j] (failing with "invalid
   split index", "the targetted instruction is not a match", "cannot find
   the constructor C", in this order), then applies:
   - when the variables read by [e] are neither read nor written by the
     prefix [hd], and [~] is [<=] or [hd] is empty (framed form):
     [t_bdhoare_rmatch_framed { k; j }];
   - otherwise (unframed form): [EcBdHoareTransform.t_bdhoare_transform]
     with [EcTrRMatch.TrRMatch { trrm_at = k; trrm_ctor = j }].

   Visible goals, in this order (those of the rule applied):
     hoare [hd : P ==> exists xs, e = C xs]
     phoare [hd; b[ys/xs]; tl : e = C ys /\ P ==> Q] ~ d             (framed)
     phoare [hd; ys <- oget (get_as_C e); b[ys/xs]; tl : P ==> Q] ~ d
                                                                   (unframed)
   Emits no node of its own. *)
val t_bdhoare_rmatch : bdhoare_rmatch_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match C k] on a [bdHoareS] goal: types the position [k] in the goal's
   memory and applies [t_bdhoare_rmatch]. *)
val process_bdhoare_rmatch : symbol -> pcodepos1 -> backward
