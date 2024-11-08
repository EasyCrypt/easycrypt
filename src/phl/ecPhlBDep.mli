(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
(* val bdep : env -> stmt -> psymbol -> variable list -> int -> variable list -> int-> psymbol -> unit *)

val t_bdep_form : variable list -> form -> variable -> tcenv1 -> tcenv 

val t_bdep : int -> int -> variable list -> variable list -> psymbol -> psymbol -> (int -> int) option -> tcenv1 -> tcenv

val t_bdepeq : variable list * variable list -> int -> (int * variable list * variable list) list -> form option -> tcenv1 -> tcenv

val t_circ : tcenv1 -> tcenv
  
val process_bdep : bdep_info -> tcenv1 -> tcenv

val process_bdepeq : bdepeq_info -> tcenv1 -> tcenv

val process_bdep_form  : bdepvar list -> pformula -> bdepvar -> tcenv1 -> tcenv
