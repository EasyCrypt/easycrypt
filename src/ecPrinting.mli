(* -------------------------------------------------------------------- *)
open EcSymbols
open EcFormat
open EcPath
open EcUidgen
open EcParsetree
open EcTypes
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
val pp_located : Location.t -> 'a pp -> 'a pp

(* -------------------------------------------------------------------- *)
val pp_qsymbol : qsymbol pp
val pp_path    : EcPath.path pp

(* -------------------------------------------------------------------- *)
(* AST pretty-printing                                                  *)

val pp_type : ?vmap:NameGen.t -> ty pp
val pp_dom  : (ty list) pp

val pp_tydecl : EcEnv.env -> (path * tydecl) pp
val pp_opdecl : (path * operator) pp

