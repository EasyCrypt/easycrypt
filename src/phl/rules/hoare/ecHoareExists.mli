(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type hoare_exists_elim = {
  hxe_bound : int option;   (* at most that many binders; all if none *)
}

(* [t_hoareS_exists_elim { hxe_bound = b }] — elimination of the
   existentials of the precondition:

     forall xs, hoare [c : P' ==> Q | E]
     -----------------------------------  (xs, P') = prenex_b(P)
            hoare [c : P ==> Q | E]

   where [prenex_b(P)] is [EcPlExists.prenex_exists ?bound:b P]: [P]
   with (at most [b] of) its existential binders [xs] pulled to the
   front, freshened; [P] entails [exists xs, P'], and [xs] occur nowhere
   else. When [P] has no binder to pull, [xs] is empty and the premise is
   the conclusion.

   Node: [RHoareSExistsElim { hxe_bound = b }].
   Checker: "hoareS-exists-elim". *)
val t_hoareS_exists_elim : hoare_exists_elim -> backward

(* [t_hoareF_exists_elim { hxe_bound = b }] — same for a procedure:

     forall xs, hoare [f : P' ==> Q | E]
     -----------------------------------  (xs, P') = prenex_b(P)
            hoare [f : P ==> Q | E]

   Node: [RHoareFExistsElim { hxe_bound = b }].
   Checker: "hoareF-exists-elim". *)
val t_hoareF_exists_elim : hoare_exists_elim -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_hoare_exists_elim r] — [t_hoareS_exists_elim r] or
   [t_hoareF_exists_elim r], depending on the goal. *)
val t_hoare_exists_elim : hoare_exists_elim -> backward

(* [t_hoare_exists_intro fs] — on [hoare [c : P ==> Q | E]] (or on a
   procedure [f]), [fs] formulas in the memory of the judgement, with
   [xs] fresh locals named after [fs] ([EcPlExists.intro_binders]):
   1. the consequence rule (currently [EcPhlConseq.t_conseq]) to
      [hoare [c : exists xs, (/\_i xs_i = fs_i) /\ P ==> Q | E]];
   2. its premise [forall &m, P => exists xs, ...] is closed by giving
      [fs] as witnesses, its premise [Q => Q] by [trivial].
   Visible goal: the judgement of 1. Emits no node of its own. *)
val t_hoare_exists_intro : ss_inv list -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [exists* fs] / [exlim fs] ([~elim]) on a [hoareS] or [hoareF] goal:
   [fs] typed in the memory of the judgement; [t_hoare_exists_intro],
   followed for [exlim] by [t_hoare_exists_elim] on as many binders as
   there are formulas. *)
val process_hoare_exists_intro :
  elim:bool -> EcParsetree.pformula list -> backward
