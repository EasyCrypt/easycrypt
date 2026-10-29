(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_exists_elim = {
  exe_bound : int option;   (* at most that many binders; all if none *)
}

(* [t_equivS_exists_elim { exe_bound = b }] — elimination of the
   existentials of the precondition:

     forall xs, equiv [c1 ~ c2 : P' ==> Q]
     -------------------------------------  (xs, P') = prenex_b(P)
            equiv [c1 ~ c2 : P ==> Q]

   where [prenex_b(P)] is [EcPlExists.prenex_exists ?bound:b P]: [P]
   with (at most [b] of) its existential binders [xs] pulled to the
   front, freshened; [P] entails [exists xs, P'], and [xs] occur nowhere
   else. When [P] has no binder to pull, [xs] is empty and the premise is
   the conclusion.

   Node: [REquivSExistsElim { exe_bound = b }].
   Checker: "equivS-exists-elim". *)
val t_equivS_exists_elim : equiv_exists_elim -> backward

(* [t_equivF_exists_elim { exe_bound = b }] — same for procedures:

     forall xs, equiv [f1 ~ f2 : P' ==> Q]
     -------------------------------------  (xs, P') = prenex_b(P)
            equiv [f1 ~ f2 : P ==> Q]

   Node: [REquivFExistsElim { exe_bound = b }].
   Checker: "equivF-exists-elim". *)
val t_equivF_exists_elim : equiv_exists_elim -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_equiv_exists_elim r] — [t_equivS_exists_elim r] or
   [t_equivF_exists_elim r], depending on the goal. *)
val t_equiv_exists_elim : equiv_exists_elim -> backward

(* [t_equiv_exists_intro fs] — on [equiv [c1 ~ c2 : P ==> Q]] (or on
   procedures [f1 ~ f2]), [fs] formulas in the memories of the judgement,
   with [xs] fresh locals named after [fs] ([EcPlExists.intro_binders]):
   1. the consequence rule (currently [EcPhlConseq.t_conseq]) to
      [equiv [c1 ~ c2 : exists xs, (/\_i xs_i = fs_i) /\ P ==> Q]];
   2. its premise [forall &1 &2, P => exists xs, ...] is closed by giving
      [fs] as witnesses, its premise [Q => Q] by [trivial].
   Visible goal: the judgement of 1. Emits no node of its own. *)
val t_equiv_exists_intro : ts_inv list -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [exists* fs] / [exlim fs] ([~elim]) on an [equivS] or [equivF] goal:
   [fs] typed in the memories of the judgement; [t_equiv_exists_intro],
   followed for [exlim] by [t_equiv_exists_elim] on as many binders as
   there are formulas. *)
val process_equiv_exists_intro :
  elim:bool -> EcParsetree.pformula list -> backward
