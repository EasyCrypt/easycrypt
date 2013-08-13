open EcUtils
open EcParsetree
open EcUtils
open EcMaps
open EcIdent
open EcTypes
open EcFol

module Sp = EcPath.Sp

exception UnknownSubgoal of int
exception NotAnOpenGoal of int option
exception InvalidNumberOfTactic of int * int
exception StillOpenGoal of int
exception NotReducible

let pp_error fmt = function
  | StillOpenGoal i ->
      Format.fprintf fmt "Still open goal %i, please report" i
  | UnknownSubgoal i ->
      Format.fprintf fmt "Unknown subgoal %i, please report" i
  | NotAnOpenGoal (Some i) ->
      Format.fprintf fmt "Not a open goal %i, please report" i
  | InvalidNumberOfTactic(i1,i2) -> 
      Format.fprintf fmt 
        "Invalid number of tactic, %i tactics expected, %i given" i1 i2 
  | e -> raise e

let _ = EcPException.register pp_error

type local_kind =
  | LD_var   of ty * form option
  | LD_mem   of EcMemory.memtype
  | LD_modty of EcModules.module_type * EcModules.mod_restr
  | LD_hyp   of form  (* of type bool *)

type l_local = EcIdent.t * local_kind

type hyps = {
    h_tvar  : EcIdent.t list;
    h_local : l_local list;
  }

(* -------------------------------------------------------------------- *)
(*    Basic construction for building the logic                         *)
(* -------------------------------------------------------------------- *)

type prover_info = unit (* FIXME *)

type tac_pos = int EcParsetree.doption

type i_pat =
  | IPpat
  | IPif of s_pat * s_pat
  | IPwhile of s_pat 
and s_pat = (int (* index of targetted instr. *) * i_pat) list


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
  | RN_sp 
	(* Field & Ring*)
  | RN_field 
  | RN_field_simp 
  | RN_ring

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
  | RN_hl_equiv_rnd of (form,form,form) EcParsetree.rnd_tac_info
  | RN_hl_conseq 
  | RN_hl_conseq_bd
  | RN_hl_exfalso 
  | RN_hl_hoare_equiv 
  | RN_hl_deno      
  | RN_hl_hoare_bd_hoare      
  | RN_hl_prbounded      
  | RN_hl_prfalse      
  | RN_hl_pr_lemma
  | RN_hl_bdeq      
  | RN_hl_fel       of (form * form * form * form * (EcPath.xpath*form) list)

  | RN_bhl_rnd of (form,ty->form option,ty->form) EcParsetree.rnd_tac_info
  | RN_eqobs_in
  | RN_notmod
  | RN_hl_exists_elim 
  | RN_hoare_true
  | RN_equiv_trans 

type 'a rule_arg = 
  | RA_form of EcFol.form             (* formula             *)
  | RA_id   of EcIdent.t              (* local ident         *)
  | RA_mp   of EcPath.mpath           (* module              *)
  | RA_node of 'a                    (* sub-derivation      *)

type 'a rule = {
  pr_name : rule_name;
  pr_hyps : 'a rule_arg list;
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

let pp_tac_error fmt error =
  match error with
  | UnknownAx p ->
    Format.fprintf fmt "Unknown axiom/lemma %s" (EcPath.tostring p)
  | NotAHypothesis id ->
    Format.fprintf fmt "Unknown hypothesis %s" (EcIdent.name id)
  | TooManyArguments ->
    Format.fprintf fmt "Too many arguments in the application"
  | InvalNumOfTactic (i1,i2) ->
    Format.fprintf fmt "Invalid number of tactics: %i given, %i expected" i2 i1
  | NotPhl b ->
    let s =
      match b with
      | None -> "phl/prhl"
      | Some true -> "phl"
      | Some false -> "prhl" in
    Format.fprintf fmt "The conclusion does not end by a %s judgment" s
  | InvalidCodePosition (msg,k,lb,up) ->
    Format.fprintf fmt "%s: Invalid code line number %i, expected in [%i,%i]" msg k lb up
  | NoSkipStmt ->
    Format.fprintf fmt "Cannot apply skip rule"
  | InvalidExfalso ->
    Format.fprintf fmt "Cannot apply exfalso: pre-condition is not false"   
  | InvalidName x ->
    Format.fprintf fmt "Invalid name for this kind of object: %s" x
  | User msg ->
    Format.fprintf fmt "%s" msg

let _ = EcPException.register (fun fmt exn ->
  match exn with
  | TacError (_, error) -> pp_tac_error fmt error
  | _ -> raise exn)

(* -------------------------------------------------------------------- *)
let tacerror ?(catchable = true) error =
  raise (TacError (catchable, error))

let tacuerror ?(catchable = true) fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _ ->
         Format.pp_print_flush fbuf ();
         raise (TacError (catchable, User (Buffer.contents buf))))
      fbuf fmt

(* -------------------------------------------------------------------- *)
let rec jucdepends sp juc =
  let sp =
    match juc.j_rule.pr_name with
    | RN_glob (p, _) -> Sp.add p sp
    | _ -> sp
  in
    List.fold_left jucdepends sp
      (List.pmap
         (function RA_node x -> Some x | _ -> None)
         juc.j_rule.pr_hyps)

let jucdepends juc = jucdepends Sp.empty juc
