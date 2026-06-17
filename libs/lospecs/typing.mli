(* -------------------------------------------------------------------- *)
open Ptree
open Ast

(* -------------------------------------------------------------------- *)
(* Type-check a parsed lospecs program, returning each named definition
   with its elaborated body. *)
val tt_program : pprogram -> (symbol * adef) list
