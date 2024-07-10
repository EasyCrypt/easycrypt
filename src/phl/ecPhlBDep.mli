(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcCoreGoal
open EcPath
open EcAst

(* -------------------------------------------------------------------- *)
(* val bdep : env -> stmt -> psymbol -> variable list -> int -> variable list -> int-> psymbol -> unit *)

val t_bdep : variable list -> int -> variable list -> int -> psymbol -> psymbol -> tcenv1 -> tcenv

val t_circ : tcenv1 -> tcenv
  
val process_bdep : (string list * int) -> (string list * int) -> psymbol -> psymbol -> tcenv1 -> tcenv
