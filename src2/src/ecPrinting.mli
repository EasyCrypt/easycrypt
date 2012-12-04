(* -------------------------------------------------------------------- *)
open EcSymbols
open EcUidgen
open EcTypes
open EcParsetree
open EcTypedtree

(* -------------------------------------------------------------------- *)
val err : (Format.formatter -> 'a -> unit) -> 'a -> unit

(* -------------------------------------------------------------------- *)
val pp_located :    Location.t
                 -> (Format.formatter -> 'a -> unit)
                 -> Format.formatter
                 -> 'a
                 -> unit

(* -------------------------------------------------------------------- *)
(* AST Pretty-Printing                                                  *)
val pp_type : ?vmap:NameGen.t -> Format.formatter -> ty -> unit

(* -------------------------------------------------------------------- *)
(* Errors Pretty-Printing                                               *)
val pp_typerror : Format.formatter -> tyerror -> unit
