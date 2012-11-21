open Utils
open Parsetree

type params_decl = (symbol * tyexpr) list

type form = 
  | PFexpr   of expr
  | PFapp    of qsymbol * form list
  | PFif     of form * form * form
  | PFlet    of lpattern * form * form
  | PFforall of params_decl * form
  | PFexists of params_decl * form

 
