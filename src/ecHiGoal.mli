(* -------------------------------------------------------------------- *)
open EcLocation
open EcSymbols
open EcParsetree
open EcFol
open EcCoreGoal
open EcCoreGoal.FApi
open EcProofTerm

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_provers   : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode   : [`Admit | `Strict | `Sloppy | `Report];
  tt_implicits : bool;
  tt_oldip     : bool;
  tt_redlogic  : bool;
  tt_und_delta : bool;
}

type engine  = ptactic_core -> backward

(* -------------------------------------------------------------------- *)
type cut_t       = intropattern * pformula * (ptactics located) option
type cutdef_t    = intropattern * pcutdef
type apply_t     = EcParsetree.apply_info
type focus_t     = EcParsetree.tfocus
type cutmode     = [`Have | `Suff]

(* -------------------------------------------------------------------- *)
val process_tfocus : tcenv -> focus_t -> tfocus

(* -------------------------------------------------------------------- *)
module LowRewrite : sig
  open EcLowGoal

  type error =
  | LRW_NotAnEquation
  | LRW_NothingToRewrite
  | LRW_InvalidOccurence
  | LRW_CannotInfer
  | LRW_IdRewriting
  | LRW_RPatternNoMatch
  | LRW_RPatternNoRuleMatch

  exception RewriteError of error

  val find_rewrite_patterns:
    rwside -> pt_ev -> (pt_ev * rwmode * (form * form)) list

  type rwinfos = rwside * EcFol.form option * EcMatching.occ option

  val t_rewrite_r:
      ?mode:[ `Full | `Light] ->
      ?target:EcIdent.t -> rwinfos -> pt_ev -> backward

  val t_rewrite:?target:EcIdent.t -> rwinfos -> proofterm -> backward

  val t_autorewrite: EcPath.path list -> backward
end

(* -------------------------------------------------------------------- *)
val t_apply_prept : prept -> backward
val t_rewrite_prept: LowRewrite.rwinfos -> prept -> backward

(* -------------------------------------------------------------------- *)
val process_reflexivity : backward
val process_assumption  : backward
val process_mintros     : ?cf:bool -> ttenv -> intropattern list -> tactical
val process_intros      : ?cf:bool -> ttenv -> intropattern list -> backward
val process_mgenintros  : ?cf:bool -> ttenv -> introgenpattern list -> tactical
val process_genintros   : ?cf:bool -> ttenv -> introgenpattern list -> backward
val process_generalize  : ?doeq:bool -> genpattern list -> backward
val process_move        : ?doeq:bool -> ppterm list -> prevert -> backward
val process_clear       : psymbol list -> backward
val process_smt         : ?loc:EcLocation.t -> ttenv -> pprover_infos -> backward
val process_apply       : implicits:bool -> apply_t * prevert option -> backward
val process_delta       : und_delta:bool -> ?target:psymbol -> (rwside * rwocc * pformula) -> backward
val process_rewrite     : ttenv -> ?target:psymbol -> rwarg list -> backward
val process_subst       : pformula list -> backward
val process_cut         : ?mode:cutmode -> engine -> ttenv -> cut_t -> backward
val process_cutdef      : ttenv -> cutdef_t -> backward
val process_left        : backward
val process_right       : backward
val process_split       : backward
val process_elim        : prevert * pqsymbol option -> backward
val process_case        : ?doeq:bool -> prevertv -> backward
val process_exists      : ppt_arg located list -> backward
val process_congr       : backward
val process_solve       : ?bases:symbol list -> ?depth:int -> backward
val process_trivial     : backward
val process_change      : pformula -> backward
val process_simplify    : preduction -> backward
val process_cbv         : preduction -> backward
val process_pose        : psymbol -> ptybindings -> rwocc -> pformula -> backward
val process_memory      : psymbol -> backward
val process_done        : backward
val process_wlog        : suff:bool -> psymbol list -> pformula -> backward
val process_genhave     : ttenv -> pgenhave -> backward

(* -------------------------------------------------------------------- *)
val process_algebra : [`Solve] -> [`Ring|`Field] -> psymbol list -> backward

(* -------------------------------------------------------------------- *)
val process_crushmode : crushmode -> bool * backward option
