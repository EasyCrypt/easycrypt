(* -------------------------------------------------------------------- *)
open Symbols
open Parsetree

(* -------------------------------------------------------------------- *)
type params_decl = (symbol * pty) list

type form = 
  | PFexpr   of pexpr
  | PFapp    of qsymbol * form list
  | PFif     of form * form * form
  | PFlet    of lpattern * form * form
  | PFforall of params_decl * form
  | PFexists of params_decl * form
