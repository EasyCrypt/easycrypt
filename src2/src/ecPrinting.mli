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
val pp_qsymbol :  Format.formatter -> qsymbol -> unit

(* -------------------------------------------------------------------- *)
(* AST Pretty-Printing                                                  *)
val pp_type : ?vmap:NameGen.t -> Format.formatter -> ty -> unit
val pp_dom : Format.formatter -> ty list -> unit

