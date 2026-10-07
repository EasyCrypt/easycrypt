(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcCoreGoal.FApi
open EcMatching.Position

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_rmatch_framed = {
  ermf_side : side;          (* side of the match *)
  ermf_at   : nm_codepos1;   (* position k of the match (resolved) *)
  ermf_ctor : int;           (* index j of the constructor C *)
}

(* [t_equiv_rmatch_framed { ermf_side = `Left; ermf_at = k; ermf_ctor = j }]
   — framed form of [match C {1} k], on an empty prefix. With
   [c = i; tl] ([k = 0]) and [i = match e with ... | C xs => b | ...], [C]
   its [j]-th constructor:

       forall &2, hoare [skip : P ==> exists xs, e = C xs]
       equiv [b[ys/xs]; tl ~ d : e{1} = C ys{1} /\ P ==> Q]
     ------------------------------------------------------  k = 0
                  equiv [c ~ d : P ==> Q]

   (symmetrically for [`Right]), where [P] is read on [&1] in the first
   premise and [ys] are fresh program variables, added to the memory of
   the left program in the second one. Side conditions: [i] is a [match]
   with a [j]-th constructor; the prefix [c[0..k)] is empty (and so,
   trivially, does not read or write [e]).

   This is not a program transformation: [e = C ys] goes to the
   precondition. It is retained as a separate rule pending a later
   discussion (the unframed form of [match C k] is the program
   transformation [EcTrRMatch]). It is sound because the empty prefix
   terminates: the first premise yields [ys] with [e = C ys] in every
   initial memory satisfying [P]. With a non-empty prefix, the initial
   memories in which it does not terminate would not be covered by the
   second premise, which is unsound for an equiv judgement.

   Node: [REquivRMatchFramed { ermf_side; ermf_at = k; ermf_ctor = j }].
   Checker: "equiv-rmatch-framed" (it re-checks the side conditions). *)
val t_equiv_rmatch_framed : equiv_rmatch_framed -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

type equiv_rmatch_rule = {
  ermr_side : side;       (* side of the match *)
  ermr_at   : codepos1;   (* position k of the match, on that side *)
  ermr_ctor : symbol;     (* constructor C of the branch taken *)
}

(* [t_equiv_rmatch { ermr_side = `Left; ermr_at = k; ermr_ctor = C }] —
   decides the match [i = c[k]] of the left program of
   [equiv [c ~ d : P ==> Q]] in favour of its [C] branch, with
   [c = hd; i; tl] (symmetrically for [`Right]). Resolves [k] to an index
   and [C] to its index [j] (failing with "invalid split index", "the
   targetted instruction is not a match", "cannot find the constructor C",
   in this order), then applies:
   - when [hd] is empty (framed form): [t_equiv_rmatch_framed];
   - otherwise (unframed form): [EcEquivTransform.t_equiv_transform] on
     that side with [EcTrRMatch.TrRMatch { trrm_at = k; trrm_ctor = j }].

   Visible goals, in this order (those of the rule applied):
     forall &2, hoare [hd : P ==> exists xs, e = C xs]
     equiv [b[ys/xs]; tl ~ d : e{1} = C ys{1} /\ P ==> Q]            (framed)
     equiv [hd; ys <- oget (get_as_C e); b[ys/xs]; tl ~ d : P ==> Q]
                                                                   (unframed)
   Emits no node of its own. *)
val t_equiv_rmatch : equiv_rmatch_rule -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [match C {i} k] on an [equivS] goal: types the position [k] in the
   memory of side [i] and applies [t_equiv_rmatch]. *)
val process_equiv_rmatch : side -> symbol -> pcodepos1 -> backward
