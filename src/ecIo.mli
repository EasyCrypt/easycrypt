(* -------------------------------------------------------------------- *)
type ecreader

(* -------------------------------------------------------------------- *)
val from_channel : ?close:bool -> name:string -> in_channel -> ecreader
val from_file    : string -> ecreader
val from_string  : string -> ecreader

(* -------------------------------------------------------------------- *)
module Notations : sig
  (* Callback driving template lookup at parse time. Receives the full
     qualified symbol of the notation reference (e.g. `["Dst"], "#foo"`)
     and returns the template items if one is registered. *)
  type t = EcSymbols.qsymbol -> EcDecl.nt_template_item list option

  val empty : t
end

(* -------------------------------------------------------------------- *)
val finalize : ecreader -> unit
val xparse   : ?notations:Notations.t -> ecreader -> string * EcParsetree.prog
val parse    : ?notations:Notations.t -> ecreader -> EcParsetree.prog
val parseall : ?notations:Notations.t -> ecreader -> EcParsetree.global list
val drain    : ecreader -> unit
val lexbuf   : ecreader -> Lexing.lexbuf

(* -------------------------------------------------------------------- *)
val lex_single_token : string -> EcParser.token option
val lex_only_token   : string -> EcParser.token option
val is_sym_ident : string -> bool
val is_op_ident  : string -> bool
val is_mem_ident : string -> bool
val is_mod_ident : string -> bool

(* -------------------------------------------------------------------- *)
val is_binop     : string -> [`Yes | `No | `Invalid]
val is_uniop     : string -> [`Yes | `No | `Invalid]
