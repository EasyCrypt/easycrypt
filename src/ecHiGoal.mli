(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcFol
open EcEnv
open EcCoreGoal
open EcCoreGoal.FApi
open EcProofTerm

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_provers   : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode   : [`Admit | `Strict | `Standard | `Report];
  tt_implicits : bool;
}

type smtinfo = pdbhint option * pprover_infos
type engine  = ptactic_core -> backward

(* -------------------------------------------------------------------- *)
type cut_t    = intropattern * pformula * (ptactics located) option
type cutdef_t = intropattern * pcutdef
type apply_t  = EcParsetree.apply_info
type focus_t  = EcParsetree.tfocus

(* -------------------------------------------------------------------- *)
val process_tfocus : tcenv -> focus_t -> tfocus

(* -------------------------------------------------------------------- *)
module LowApply : sig
  val t_apply_bwd_r : pt_ev -> backward
  val t_apply_bwd   : proofterm -> backward
end

(* -------------------------------------------------------------------- *)
module LowRewrite : sig
  type error =
  | LRW_NotAnEquation
  | LRW_NothingToRewrite
  | LRW_InvalidOccurence
  | LRW_CannotInfer

  exception RewriteError of error

  val find_rewrite_pattern:
    rwside -> LDecl.hyps -> pt_ev -> pt_ev * (form * form)

  val t_rewrite_r:
    rwside * EcMatching.occ option -> pt_ev -> backward

  val t_rewrite:
    rwside * EcMatching.occ option -> proofterm -> backward

  val t_autorewrite: EcPath.path list -> backward
end

(* -------------------------------------------------------------------- *)
val t_apply_prept : prept -> backward
val t_rewrite_prept: rwside * EcMatching.occ option -> prept -> backward

(* -------------------------------------------------------------------- *)
val process_reflexivity : backward
val process_assumption  : backward
val process_intros      : ?cf:bool -> intropattern -> backward
val process_mintros     : ?cf:bool -> intropattern -> tactical
val process_generalize  : genpattern list -> backward
val process_clear       : psymbol list -> backward
val process_smt         : ?loc:EcLocation.t -> ttenv -> smtinfo -> backward
val process_apply       : implicits:bool -> apply_t -> backward
val process_delta       : (rwside * EcMatching.occ option * pformula) -> backward
val process_rewrite     : ttenv -> rwarg list -> backward
val process_subst       : pformula list -> backward
val process_cut         : engine -> cut_t -> backward
val process_cutdef      : cutdef_t -> backward
val process_left        : backward
val process_right       : backward
val process_split       : backward
val process_elim        : genpattern list * pqsymbol option -> backward
val process_case        : genpattern list -> backward
val process_exists      : ppt_arg located list -> backward
val process_congr       : backward
val process_trivial     : backward
val process_change      : pformula -> backward
val process_simplify    : preduction -> backward
val process_pose        : psymbol -> rwocc -> pformula -> backward
val process_done        : backward

(* -------------------------------------------------------------------- *)
val process_algebra : [`Solve] -> [`Ring|`Field] -> psymbol list -> backward
