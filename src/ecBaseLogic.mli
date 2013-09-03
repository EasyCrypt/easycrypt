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
  | LD_modty of EcModules.module_type * EcModules.mod_restr
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

class virtual xrule : string ->
object
  method name : string
end

type rule =
| RN_admit
| RN_conv
| RN_intro      of [`Raw of EcIdent.t list | `Exist]
| RN_elim       of [`Exist]
| RN_weak       of Sid.t
| RN_apply
| RN_smt
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

val tacerror  : ?catchable:bool -> tac_error -> 'a
val tacuerror : ?catchable:bool -> ('a, Format.formatter, unit, 'b) format4 -> 'a
