(* -------------------------------------------------------------------- *)
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type bdhoare_exists_elim = {
  bxe_bound : int option;   (* at most that many binders; all if none *)
}

(* [t_bdhoareS_exists_elim { bxe_bound = b }] — elimination of the
   existentials of the precondition, [~ d] the goal's comparison and
   bound (any comparison):

     forall xs, phoare [c : P' ==> Q] ~ d
     ------------------------------------  (xs, P') = prenex_b(P)
            phoare [c : P ==> Q] ~ d

   where [prenex_b(P)] is [EcPlExists.prenex_exists ?bound:b P]: [P]
   with (at most [b] of) its existential binders [xs] pulled to the
   front, freshened; [P] entails [exists xs, P'], and [xs] occur nowhere
   else (in particular, not in [d]). When [P] has no binder to pull, [xs]
   is empty and the premise is the conclusion.

   Node: [RBdHoareSExistsElim { bxe_bound = b }].
   Checker: "bdhoareS-exists-elim". *)
val t_bdhoareS_exists_elim : bdhoare_exists_elim -> backward

(* [t_bdhoareF_exists_elim { bxe_bound = b }] — same for a procedure:

     forall xs, phoare [f : P' ==> Q] ~ d
     ------------------------------------  (xs, P') = prenex_b(P)
            phoare [f : P ==> Q] ~ d

   Node: [RBdHoareFExistsElim { bxe_bound = b }].
   Checker: "bdhoareF-exists-elim". *)
val t_bdhoareF_exists_elim : bdhoare_exists_elim -> backward

(* ==================================================================== *)
(* Derived tactics                                                      *)

(* [t_bdhoare_exists_elim r] — [t_bdhoareS_exists_elim r] or
   [t_bdhoareF_exists_elim r], depending on the goal. *)
val t_bdhoare_exists_elim : bdhoare_exists_elim -> backward

(* [t_bdhoare_exists_intro fs] — on [phoare [c : P ==> Q] ~ d] (or on a
   procedure [f]), [fs] formulas in the memory of the judgement, with
   [xs] fresh locals named after [fs] ([EcPlExists.intro_binders]):
   1. the consequence rule (currently [EcPhlConseq.t_conseq]) to
      [phoare [c : exists xs, (/\_i xs_i = fs_i) /\ P ==> Q] ~ d];
   2. its premise [forall &m, P => exists xs, ...] is closed by giving
      [fs] as witnesses, its premise on the postcondition by [trivial].
   Visible goal: the judgement of 1. Emits no node of its own. *)
val t_bdhoare_exists_intro : ss_inv list -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [exists* fs] / [exlim fs] ([~elim]) on a [bdHoareS] or [bdHoareF]
   goal: [fs] typed in the memory of the judgement;
   [t_bdhoare_exists_intro], followed for [exlim] by
   [t_bdhoare_exists_elim] on as many binders as there are formulas. *)
val process_bdhoare_exists_intro :
  elim:bool -> EcParsetree.pformula list -> backward
