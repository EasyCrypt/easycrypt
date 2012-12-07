(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUidgen
open EcTypes
open EcParsetree

(* -------------------------------------------------------------------- *)
val err : (Format.formatter -> 'a -> unit) -> 'a -> unit

(* -------------------------------------------------------------------- *)
val pp_located :    Location.t
                 -> (Format.formatter -> 'a -> unit)
                 -> Format.formatter
                 -> 'a
                 -> unit

(* -------------------------------------------------------------------- *)
val pp_list :
           ?pre:('a, 'b, 'c, 'd, 'd, 'a) format6 ->
           ?sep:('e, 'f, 'g, 'h, 'h, 'e) format6 ->
           ?post:('i, 'j, 'k, 'l, 'l, 'i) format6 ->
           (Format.formatter -> 'm -> unit) ->
           Format.formatter -> 'm list -> unit

val pp_path : Format.formatter -> EcPath.path -> unit

(* -------------------------------------------------------------------- *)
val pp_qsymbol :  Format.formatter -> qsymbol -> unit

(* -------------------------------------------------------------------- *)
(* AST Pretty-Printing                                                  *)
val pp_type : ?vmap:NameGen.t -> Format.formatter -> ty -> unit
val pp_dom : Format.formatter -> ty list -> unit

