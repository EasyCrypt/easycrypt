(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_rmatch_framed = {
  ehrmf_at   : nm_codepos1;   (* position k of the match (resolved) *)
  ehrmf_ctor : int;           (* index j of the constructor C *)
}

(* [t_ehoare_rmatch_framed { ehrmf_at = k; ehrmf_ctor = j }] — framed form
   of [match C k]. With [c = hd; i; tl], [hd = c[0..k)] and
   [i = c[k] = match e with ... | C xs => b | ...], [C] its [j]-th
   constructor:

       hoare [hd : P ==> exists xs, e = C xs]
       ehoare [hd; b[ys/xs]; tl : (e = C ys /\ P) `|` f ==> Q]
     ---------------------------------------------------------  e indep. of hd
                  ehoare [c : P `|` f ==> Q]

   where [ys] are fresh program variables, added to the memory of the
   second premise. Side conditions: [i] is a [match] with a [j]-th
   constructor; the variables read by [e] are neither read nor written by
   [hd]; the precondition has the form [P `|` f] (otherwise fails with "the
   pre should have the form \"_ `|` _\"").

   This is not a program transformation: [e = C ys] goes to the
   precondition, so the rule is stated on the whole statement (implicit
   seq around the match). It is retained as a separate rule pending a
   later discussion (the unframed form of [match C k] is the program
   transformation [EcTrRMatch]). It is sound because [e] has the same
   value before and after [hd], and because the initial memories in which
   [hd] does not terminate contribute nothing to the expectation of [Q]:
   in the other ones, the first premise yields [ys] with [e = C ys]
   initially.

   Node: [REHoareRMatchFramed { ehrmf_at = k; ehrmf_ctor = j }].
   Checker: "ehoare-rmatch-framed" (it re-checks the side conditions). *)
val t_ehoare_rmatch_framed : ehoare_rmatch_framed -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

type ehoare_rmatch_rule = {
  ehrmr_at   : codepos1;   (* position k of the match *)
  ehrmr_ctor : symbol;     (* constructor C of the branch taken *)
}

(* [t_ehoare_rmatch { ehrmr_at = k; ehrmr_ctor = C }] — decides the match
   [i = c[k]] of [ehoare [c : P `|` f ==> Q]] in favour of its [C] branch.
   Resolves [k] to an index and [C] to its index [j] (failing with "invalid
   split index", "the targetted instruction is not a match", "cannot find
   the constructor C", in this order), then applies:
   - when the variables read by [e] are neither read nor written by the
     prefix [hd] (framed form): [t_ehoare_rmatch_framed { k; j }];
   - otherwise (unframed form): [EcEHoareTransform.t_ehoare_transform]
     with [EcTrRMatch.TrRMatch { trrm_at = k; trrm_ctor = j }].
   Both fail with "the pre should have the form \"_ `|` _\"" when the
   precondition is not of that form.

   Visible goals, in this order (those of the rule applied):
     hoare [hd : P ==> exists xs, e = C xs]
     ehoare [hd; b[ys/xs]; tl : (e = C ys /\ P) `|` f ==> Q]         (framed)
     ehoare [hd; ys <- oget (get_as_C e); b[ys/xs]; tl : P `|` f ==> Q]
                                                                   (unframed)
   Emits no node of its own. *)
val t_ehoare_rmatch : ehoare_rmatch_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match C k] on an [eHoareS] goal: types the position [k] in the goal's
   memory and applies [t_ehoare_rmatch]. *)
val process_ehoare_rmatch : symbol -> pcodepos1 -> backward
