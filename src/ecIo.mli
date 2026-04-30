(* -------------------------------------------------------------------- *)
type ecreader

(* -------------------------------------------------------------------- *)
val from_channel : ?close:bool -> name:string -> in_channel -> ecreader
val from_file    : string -> ecreader
val from_string  : string -> ecreader

(* -------------------------------------------------------------------- *)
val finalize : ecreader -> unit
val xparse   : ecreader -> string * EcParsetree.prog
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
