(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_rmatch_framed = {
  hrmf_at   : nm_codepos1;   (* position k of the match (resolved) *)
  hrmf_ctor : int;           (* index j of the constructor C *)
}

(* [t_hoare_rmatch_framed { hrmf_at = k; hrmf_ctor = j }] — framed form of
   [match C k]. With [c = hd; i; tl], [hd = c[0..k)] and
   [i = c[k] = match e with ... | C xs => b | ...], [C] its [j]-th
   constructor:

       hoare [hd : P ==> exists xs, e = C xs | E]
       hoare [hd; b[ys/xs]; tl : e = C ys /\ P ==> Q | E]
     ----------------------------------------------------  e indep. of hd
                  hoare [c : P ==> Q | E]

   where [E] are the exceptional postconditions of the goal and [ys] are
   fresh program variables, added to the memory of the second premise.
   Side conditions: [i] is a [match] with a [j]-th constructor; the
   variables read by [e] are neither read nor written by [hd].

   This is not a program transformation: [e = C ys] goes to the
   precondition, so the rule is stated on the whole statement (implicit
   seq around the match). It is retained as a separate rule pending a
   later discussion (the unframed form of [match C k] is the program
   transformation [EcTrRMatch]). It is sound because [e] has the same
   value before and after [hd], and because a hoare judgement ignores the
   initial memories in which [hd] does not terminate: in the other ones,
   the first premise yields [ys] with [e = C ys] initially.

   Node: [RHoareRMatchFramed { hrmf_at = k; hrmf_ctor = j }].
   Checker: "hoare-rmatch-framed" (it re-checks the side conditions). *)
val t_hoare_rmatch_framed : hoare_rmatch_framed -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

type hoare_rmatch_rule = {
  hrmr_at   : codepos1;   (* position k of the match *)
  hrmr_ctor : symbol;     (* constructor C of the branch taken *)
}

(* [t_hoare_rmatch { hrmr_at = k; hrmr_ctor = C }] — decides the match
   [i = c[k]] of [hoare [c : P ==> Q | E]] in favour of its [C] branch.
   Resolves [k] to an index and [C] to its index [j] (failing with "invalid
   split index", "the targetted instruction is not a match", "cannot find
   the constructor C", in this order), then applies:
   - when the variables read by [e] are neither read nor written by the
     prefix [hd] (framed form): [t_hoare_rmatch_framed { k; j }];
   - otherwise (unframed form): [EcHoareTransform.t_hoare_transform] with
     [EcTrRMatch.TrRMatch { trrm_at = k; trrm_ctor = j }].

   Visible goals, in this order (those of the rule applied):
     hoare [hd : P ==> exists xs, e = C xs | E]
     hoare [hd; b[ys/xs]; tl : e = C ys /\ P ==> Q | E]              (framed)
     hoare [hd; ys <- oget (get_as_C e); b[ys/xs]; tl : P ==> Q | E]
                                                                   (unframed)
   Emits no node of its own. *)
val t_hoare_rmatch : hoare_rmatch_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match C k] on a [hoareS] goal: types the position [k] in the goal's
   memory and applies [t_hoare_rmatch]. *)
val process_hoare_rmatch : symbol -> pcodepos1 -> backward
