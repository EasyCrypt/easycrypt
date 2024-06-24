(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcCoreGoal
open EcPath
open EcAst

(* -------------------------------------------------------------------- *)
val bdep : env -> stmt -> psymbol -> variable list -> int -> variable list -> int-> psymbol -> unit

val bdep_xpath : env -> xpath -> psymbol -> int -> int -> string list -> psymbol -> unit 

val t_bdep : variable list -> int -> variable list -> int -> psymbol -> psymbol -> tcenv1 -> tcenv
  
val process_bdep : (string list * int) -> (string list * int) -> psymbol -> psymbol -> tcenv1 -> tcenv
