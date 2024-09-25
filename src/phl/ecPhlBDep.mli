(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcCoreGoal
open EcPath
open EcAst

(* -------------------------------------------------------------------- *)
(* val bdep : env -> stmt -> psymbol -> variable list -> int -> variable list -> int-> psymbol -> unit *)

val t_bdep : variable list -> int -> variable list -> int -> psymbol -> psymbol -> tcenv1 -> tcenv

val t_bdepeq : (variable * variable) list -> int -> (variable * variable) list -> int -> tcenv1 -> tcenv

val t_circ : tcenv1 -> tcenv
  
val process_bdep : (string list * string list * int) -> (string list * int) -> psymbol -> psymbol -> tcenv1 -> tcenv

val process_bdepeq : (string list * string list * int) -> (string list * string list * int) -> tcenv1 -> tcenv
