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
  | RN_hl_append    of tac_dir * tac_pos * EcFol.form * EcFol.app_bd_info
  | RN_hl_rcond     of bool option * bool * int
  | RN_hl_case      of form
  | RN_hl_while     of EcFol.form * EcFol.form option * (EcFol.form * EcFol.form) option
  | RN_hl_fission   of bool option * codepos * (int * (int * int))
  | RN_hl_fusion    of bool option * codepos * (int * (int * int))
  | RN_hl_unroll    of bool option * codepos
  | RN_hl_splitwhile of EcTypes.expr *  bool option * codepos
  | RN_hl_call      of bool option * EcFol.form * EcFol.form
  | RN_hl_swap      of bool option * int * int * int
  | RN_hl_cfold     of bool option * codepos * int option
  | RN_hl_inline    of bool option * s_pat 
  | RN_hl_kill      of bool option * codepos * int option
  | RN_hl_alias     of bool option * codepos
  | RN_hl_hoare_rnd
  | RN_hl_equiv_rnd of rnd_tac_info
  | RN_hl_conseq 
  | RN_hl_exfalso 
  | RN_hl_hoare_equiv 
  | RN_hl_deno      
  | RN_hl_hoare_bd_hoare
  | RN_hl_prbounded      
  | RN_hl_prfalse      
  | RN_hl_pror
  | RN_hl_bdeq      
  | RN_hl_fel       of (form * form * form * form * form)

  | RN_bhl_rnd of (EcFol.form option * EcFol.form)
  | RN_eqobs_in 
  | RN_notmod

type 'a rule_arg = 
  | RA_form of EcFol.form             (* formula             *)
  | RA_id   of EcIdent.t              (* local ident         *)
  | RA_mp   of EcPath.mpath           (* module              *)
  | RA_node of 'a                     (* sub-derivation      *)

type 'a rule = {
    pr_name : rule_name;
    pr_hyps : 'a rule_arg list
  }

type l_decl = hyps * form

type judgment = {
  j_decl : l_decl;
  j_rule : judgment rule
}

(* -------------------------------------------------------------------- *)
type tac_error =
  | UnknownAx             of EcPath.path
  | NotAHypothesis        of EcIdent.t
  | TooManyArguments
  | InvalNumOfTactic      of int * int
  | NotPhl                of bool option
  | NoSkipStmt
  | InvalidExfalso
  | InvalidCodePosition   of string*int*int*int
  | InvalidName           of string
  | User                  of string

exception TacError of bool * tac_error

val tacerror  : ?catchable:bool -> tac_error -> 'a
val tacuerror : ?catchable:bool -> ('a, Format.formatter, unit, 'b) format4 -> 'a
