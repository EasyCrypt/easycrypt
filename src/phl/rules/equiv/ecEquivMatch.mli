(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

(* Below, [M] is [match e with | C_i xs_i => b_i end] and [M'] is
   [match e' with | C_i xs_i' => b_i' end], where [C_1, ..., C_n] are the
   constructors of the datatype of [e] (and [e']), in declaration order. *)

type equiv_match_onesided = {
  emo_side : side;   (* side of the [match] *)
}

(* [t_equiv_match_onesided { emo_side = `Left }] — one-sided pattern
   matching; one premise per constructor:

     equiv{&1 + ys_i} [b_i[ys_i/xs_i] ~ c' : e<1> = C_i ys_i<1> /\ P ==> Q]
     ---------------------------------------------------------  (i = 1..n)
                       equiv [M ~ c' : P ==> Q]

   (symmetrically for [`Right]), where [ys_i] are fresh program variables,
   named after the pattern variables [xs_i] and of the same types, added
   to the memory of that side (see [EcPlMatch.match_branches]). Side
   condition: the statement of that side is the single [match] (otherwise
   fails).

   Node: [REquivMatchOneSided { emo_side }].
   Checker: "equiv-match-onesided"; it recomputes the constructors from the
   goal's context. *)
val t_equiv_match_onesided : equiv_match_onesided -> backward

(* [t_equiv_match_synced] — synchronized pattern matching on the same
   datatype (possibly at different type instances):

     (Ci) forall &1 &2, P =>
            ((exists xs, e<1> = C_i xs) <=> (exists xs', e'<2> = C_i xs'))
     (Bi) forall xs_i xs_i', equiv [b_i ~ b_i' :
            e<1> = C_i xs_i /\ e'<2> = C_i xs_i' /\ P ==> Q]
     -------------------------------------------------------------  (i = 1..n)
                          equiv [M ~ M' : P ==> Q]

   where the pattern variables become universally quantified logical
   variables, and [=>] in (Ci) and [/\] in (Bi) are simplifying. Premises,
   in order: (C1)..(Cn), then (B1)..(Bn). Side conditions: each statement
   is a single [match], both on the same datatype (otherwise fails).

   Node: [REquivMatchSynced]. Checker: "equiv-match-synced"; it recomputes
   the datatype and its constructors from the goal's context. *)
val t_equiv_match_synced : backward

(* [t_equiv_match_eq] — pattern matching on equal values:

     (C)  forall &1 &2, P => e<1> = e'<2>
     (Bi) forall xs_i, equiv [b_i ~ b_i'[xs_i/xs_i'] :
            e<1> = C_i xs_i /\ e'<2> = C_i xs_i /\ P ==> Q]
     -------------------------------------------------------------  (i = 1..n)
                          equiv [M ~ M' : P ==> Q]

   where the pattern variables become universally quantified logical
   variables, and [=>] in (C) and [/\] in (Bi) are simplifying. Premises,
   in order: (C), then (B1)..(Bn). Side conditions: each statement is a
   single [match], both on the same type (otherwise fails).

   Node: [REquivMatchEq]. Checker: "equiv-match-eq"; it recomputes the
   datatype and its constructors from the goal's context. *)
val t_equiv_match_eq : backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_match_head mode]:
   - [mode = `SSided `Left], on [equiv [M; c ~ c' : P ==> Q]]
     (symmetrically for [`Right]):
     1. when [c] is not empty, [EcEquivTransform.t_equiv_transform] on that
        side with [EcTrMatchPush.TrMatchPush], giving
          equiv [match e with | C_i xs_i => { b_i; c } end ~ c' : P ==> Q];
     2. [t_equiv_match_onesided].
     Visible goals, one per constructor:
       equiv{&1 + ys_i} [b_i[ys_i/xs_i]; c ~ c' :
                         e<1> = C_i ys_i<1> /\ P ==> Q].
   - [mode = `DSided `ConstrSynced] (resp. [`DSided `Eq]), on
     [equiv [M; c ~ M'; c' : P ==> Q]]:
     1. the push of step 1 above on the left (when [c] is not empty), then
        on the right (when [c'] is not empty);
     2. [t_equiv_match_synced] (resp. [t_equiv_match_eq]).
     Visible goals: those of the rule, the branches followed by [c] (resp.
     [c']).
   Fails if the first instruction of a side is not a [match] (left checked
   first) and, for the two-sided forms, with "match statements on
   different inductive types" or, for [`Eq], "synced match requires
   matches on the same type". Emits no node of its own. *)
val t_equiv_match_head : matchmode -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* On an [equivS] goal: [match{i}], [match] and [match =] apply
   [t_equiv_match_head] with the corresponding mode. *)
val process_equiv_match : matchmode -> backward
