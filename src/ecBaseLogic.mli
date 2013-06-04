(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcUtils
open EcMaps
open EcIdent
open EcTypes
open EcFol

(* -------------------------------------------------------------------- *)
exception UnknownSubgoal of int
exception NotAnOpenGoal of int option
exception InvalidNumberOfTactic of int * int
exception StillOpenGoal of int
exception NotReducible

(* -------------------------------------------------------------------- *)
type local_kind =
  | LD_var   of ty * form option
  | LD_mem   of EcMemory.memtype
  | LD_modty of EcModules.module_type * EcPath.Sm.t
  | LD_hyp   of form

type l_local = EcIdent.t * local_kind

type hyps = {
  h_tvar  : EcIdent.t list;
  h_local : l_local list;
}

(* -------------------------------------------------------------------- *)
module LDecl : sig
  type error = 
    | UnknownSymbol   of EcSymbols.symbol 
    | UnknownIdent    of EcIdent.t
    | NotAVariable    of EcIdent.t
    | NotAHypothesis  of EcIdent.t
    | CanNotClear     of EcIdent.t * EcIdent.t
    | DuplicateIdent  of EcIdent.t
    | DuplicateSymbol of EcSymbols.symbol

  exception Ldecl_error of error

  val add_local : EcIdent.t -> local_kind -> hyps -> hyps

  val lookup : symbol -> hyps -> l_local

  val reducible_var : EcIdent.t -> hyps -> bool
  val reduce_var    : EcIdent.t -> hyps -> form
  val lookup_var    : symbol -> hyps -> EcIdent.t * ty

  val lookup_by_id     : EcIdent.t -> hyps -> local_kind
  val lookup_hyp_by_id : EcIdent.t -> hyps -> form

  val has_hyp : symbol -> hyps -> bool
  val lookup_hyp : symbol -> hyps -> EcIdent.t * form
  val get_hyp : EcIdent.t * local_kind -> EcIdent.t * form

  val has_symbol : symbol -> hyps -> bool

  val fresh_id  : hyps -> symbol -> EcIdent.t
  val fresh_ids : hyps -> symbol list -> EcIdent.t list

  val clear : EcIdent.Sid.t -> hyps -> hyps

  val ld_subst : EcFol.f_subst -> local_kind -> local_kind
end

(* -------------------------------------------------------------------- *)
type tac_pos = int EcParsetree.doption

type i_pat =
  | IPpat
  | IPif of s_pat * s_pat
  | IPwhile of s_pat 

(* the first pair value represents the number of instructions to skip *)
and s_pat = (int * i_pat) list        

type rnd_tac_info = form EcParsetree.rnd_tac_info
type prover_info  = unit

type rule_name = 
   (* Logical rules *)
  | RN_admit
  | RN_clear        of EcIdent.Sid.t 
  | RN_prover       of prover_info
  | RN_hyp          of EcIdent.t 
  | RN_glob         of EcPath.path * EcTypes.ty list
  | RN_apply        
  | RN_cut          
  | RN_intros       of EcIdent.t list 
  | RN_exists_elim  
  | RN_exists_intro 
  | RN_conv    

    (* Rings && fields *)
  | RN_field 
  | RN_field_simp 

    (* Phl rules *)    
  | RN_hl_fun_def 
  | RN_hl_fun_abs   of EcFol.form
  | RN_hl_fun_upto  of EcFol.form * EcFol.form * EcFol.form
  | RN_hl_skip
  | RN_hl_wp        of tac_pos
  (* append: bool indicates direction: true backwards *)
  | RN_hl_append    of bool * tac_pos * EcFol.form * EcFol.form option
  | RN_hl_rcond     of bool option * bool * int
  | RN_hl_case      of form
  | RN_hl_while     of EcFol.form * EcFol.form option * (EcFol.form * EcFol.form) option
  | RN_hl_fission   of bool option * codepos * (int * (int * int))
  | RN_hl_fusion    of bool option * codepos * (int * (int * int))
  | RN_hl_unroll    of bool option * codepos
  | RN_hl_splitwhile of EcTypes.expr *  bool option * codepos
  | RN_hl_call      of bool option * EcFol.form * EcFol.form
  | RN_hl_swap      of bool * int * int * int
  | RN_hl_inline    of bool option * s_pat 
  | RN_hl_kill      of bool option * codepos * int option
  | RN_hl_alias     of bool option * codepos
  | RN_hl_hoare_rnd
  | RN_hl_equiv_rnd of rnd_tac_info
  | RN_hl_conseq 
  | RN_hl_hoare_equiv 
  | RN_hl_deno      

  | RN_bhl_rnd of (EcFol.form option * EcFol.form)

and rule_arg = 
  | RA_form of EcFol.form             (* formula             *)
  | RA_id   of EcIdent.t              (* local ident         *)
  | RA_mp   of EcPath.mpath           (* module              *)
  | RA_node of int                    (* sub-derivation      *)

type rule = {
    pr_name : rule_name;
    pr_hyps : rule_arg list
  }

type l_decl = hyps * form

type pre_judgment = {
    pj_decl : l_decl;
    pj_rule : (bool * rule) option;
  }

type judgment_uc = {
    juc_count  : int;
    juc_map    : pre_judgment Mint.t;
  }

type judgment = judgment_uc

(* -------------------------------------------------------------------- *)
type goals = judgment_uc * int list
type goal  = judgment_uc * int 

val get_goal      : goal -> pre_judgment
val get_open_goal : goal -> pre_judgment

val get_first_goal : judgment_uc -> goal

val new_goal : judgment_uc -> l_decl -> goal

val upd_rule : rule -> goal -> goals
val upd_rule_done : rule -> goal -> goals

val upd_done : judgment_uc -> judgment_uc

val open_juc  : l_decl -> judgment_uc
val close_juc : judgment_uc -> judgment_uc

val find_all_goals : judgment_uc -> goals

(* -------------------------------------------------------------------- *)
type tactic = goal -> goals

val t_id : string option -> tactic

val t_on_first : goals -> tactic -> goals
val t_on_last  : goals -> tactic -> goals

val t_subgoal  : tactic list -> goals -> goals
val t_on_goals : tactic -> goals -> goals

val t_seq_subgoal : tactic -> tactic list -> tactic

val t_seq  : tactic -> tactic -> tactic
val t_lseq : tactic list -> tactic

val t_repeat : tactic -> tactic
val t_do     : int -> tactic -> tactic
val t_try    : tactic -> tactic
val t_or     : tactic -> tactic -> tactic
