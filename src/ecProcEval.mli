(* -------------------------------------------------------------------- *)
open EcPath
open EcAst

(* -------------------------------------------------------------------- *)
val eval : EcEnv.env -> xpath * expr list -> expr option
