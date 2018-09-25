(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type ecreader

(* -------------------------------------------------------------------- *)
val from_channel : name:string -> in_channel -> ecreader
val from_file    : string -> ecreader
val from_string  : string -> ecreader

(* -------------------------------------------------------------------- *)
val finalize : ecreader -> unit
val parse    : ecreader -> EcParsetree.prog
val parseall : ecreader -> EcParsetree.global list
val drain    : ecreader -> unit
val lexbuf   : ecreader -> Lexing.lexbuf

(* -------------------------------------------------------------------- *)
val lex_single_token : string -> EcParser.token option
val is_sym_ident : string -> bool
val is_op_ident  : string -> bool
val is_mem_ident : string -> bool
val is_mod_ident : string -> bool

(* -------------------------------------------------------------------- *)
val is_binop     : string -> [`Yes | `No | `Invalid]
val is_uniop     : string -> [`Yes | `No | `Invalid]
