(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcCoreGoal
open EcPath

(* -------------------------------------------------------------------- *)
val bdep : env -> xpath -> psymbol -> int -> int-> string list -> psymbol -> unit

val t_bdep : tcenv -> EcSymbols.symbol list -> int -> int -> psymbol -> psymbol -> tcenv
  
val process_bdep : (string list * int) -> (string list * int) -> psymbol -> psymbol -> tcenv1 -> tcenv
