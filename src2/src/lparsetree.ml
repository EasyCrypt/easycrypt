(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree

(* -------------------------------------------------------------------- *)
type params_decl = (symbol * pty) list

type pbinop =
  | PPand
  | PPor
  | PPimp
  | PPiff
type form = 
  | PFunit                                (* unit literal      *)
  | PFbool   of bool                      (* bool literal      *)
  | PFint    of int                       (* int. literal      *)
  | PFident  of qsymbol                   (* symbol            *)
  | PFside   of form * side         
  | PFnot    of form 
  | PFbinop  of form * pbinop * form
  | PFapp    of qsymbol * form list
  | PFif     of form * form * form
  | PFlet    of lpattern * form * form
  | PFforall of params_decl * form
  | PFexists of params_decl * form
