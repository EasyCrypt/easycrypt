(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type ehoare_exists_elim = {
  ehxe_bound : int option;   (* at most that many binders; all if none *)
}

(* [t_ehoareS_exists_elim { ehxe_bound = b }] — elimination of the
   existentials of the precondition:

     forall xs, ehoare [c : P' ==> Q]
     --------------------------------  (xs, P') = prenex_b(P)
          ehoare [c : P ==> Q]

   where [prenex_b(P)] is [EcPlExists.prenex_exists ?bound:b P]: the
   only preconditions with binders to pull are [B `|` F] ([F] if the
   boolean [B] holds, [+inf] otherwise), for which [P'] is [B' `|` F],
   [B'] being [B] with (at most [b] of) its existential binders [xs]
   pulled to the front, freshened. [B] entails [exists xs, B'], so that
   [P] is not below the infimum of the [P'] over [xs]; [xs] occur nowhere
   else.
   When [P] has no binder to pull, [xs] is empty and the premise is the
   conclusion.

   Node: [REHoareSExistsElim { ehxe_bound = b }].
   Checker: "ehoareS-exists-elim". *)
val t_ehoareS_exists_elim : ehoare_exists_elim -> backward

(* [t_ehoareF_exists_elim { ehxe_bound = b }] — same for a procedure:

     forall xs, ehoare [f : P' ==> Q]
     --------------------------------  (xs, P') = prenex_b(P)
          ehoare [f : P ==> Q]

   Node: [REHoareFExistsElim { ehxe_bound = b }].
   Checker: "ehoareF-exists-elim". *)
val t_ehoareF_exists_elim : ehoare_exists_elim -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_ehoare_exists_elim r] — [t_ehoareS_exists_elim r] or
   [t_ehoareF_exists_elim r], depending on the goal. *)
val t_ehoare_exists_elim : ehoare_exists_elim -> backward

(* [t_ehoare_exists_intro fs] — on [ehoare [c : P ==> Q]] (or on a
   procedure [f]), [fs] formulas in the memory of the judgement, with
   [xs] fresh locals named after [fs] ([EcPlExists.intro_binders]):
   1. the consequence rule (currently [EcPhlConseq.t_conseq]) to
      [ehoare [c : (exists xs, /\_i xs_i = fs_i) `|` P ==> Q]];
   2. its premise on the precondition is closed by [xle_cxr_l] and [fs]
      as witnesses, its premise on the postcondition by [trivial].
   Visible goal: the judgement of 1. Emits no node of its own. *)
val t_ehoare_exists_intro : ss_inv list -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [exists* fs] / [exlim fs] ([~elim]) on an [eHoareS] or [eHoareF]
   goal: [fs] typed in the memory of the judgement;
   [t_ehoare_exists_intro], followed for [exlim] by
   [t_ehoare_exists_elim] on as many binders as there are formulas. *)
val process_ehoare_exists_intro :
  elim:bool -> EcParsetree.pformula list -> backward
