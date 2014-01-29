(* -------------------------------------------------------------------- *)
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

type abs_uses = {
  aus_calls  : EcPath.xpath list;
  aus_reads  : (prog_var * ty) list;
  aus_writes  : (prog_var * ty) list;
}

type local_kind =
  | LD_var    of ty * form option
  | LD_mem    of EcMemory.memtype
  | LD_modty  of EcModules.module_type * EcModules.mod_restr
  | LD_hyp    of form  (* of type bool *)
  | LD_abs_st of abs_uses

type l_local = EcIdent.t * local_kind

type hyps = {
    h_tvar  : EcIdent.t list;
    h_local : l_local list;
  }

(* -------------------------------------------------------------------- *)
(*    Basic construction for building the logic                         *)
(* -------------------------------------------------------------------- *)

type tac_pos = int EcParsetree.doption

type i_pat =
  | IPpat
  | IPif of s_pat * s_pat
  | IPwhile of s_pat 
and s_pat = (int (* index of targetted instr. *) * i_pat) list

class virtual xrule (name : string) =
object
  method name = name
end

type rule =
| RN_admit
| RN_conv
| RN_intro      of [`Raw of EcIdent.t list | `Exist]
| RN_elim       of [`Exist]
| RN_weak       of Sid.t
| RN_apply
| RN_smt
| RN_revert
| RN_hypothesis of EcIdent.t
| RN_lemma      of EcPath.path * ty list
| RN_xtd        of xrule

type 'a rule_arg = 
| RA_form of EcFol.form             (* formula             *)
| RA_id   of EcIdent.t              (* local ident         *)
| RA_mp   of EcPath.mpath           (* module              *)
| RA_node of 'a                     (* sub-derivation      *)

type 'a rnode = {
  pr_name : rule;
  pr_hyps : 'a rule_arg list
}

type l_decl = hyps * form

type judgment = {
  j_decl : l_decl;
  j_rule : judgment rnode;
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
