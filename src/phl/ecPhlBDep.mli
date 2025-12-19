(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
(* val bdep : env -> stmt -> psymbol -> variable list -> int -> variable list -> int-> psymbol -> unit *)

val t_bdep_form : form -> variable -> tcenv1 -> tcenv 

val t_bdep : ?debug:bool -> int -> int -> (variable * (int * int) option) list -> (variable * (int * int) option) list -> psymbol -> psymbol -> (int -> int) option -> tcenv1 -> tcenv

val t_bdepeq : variable list * variable list -> int -> (int * variable list * variable list) list -> form option -> bool -> tcenv1 -> tcenv

val t_bdep_eval :  int ->  int ->  variable list ->  variable list ->  psymbol ->  form list -> bool -> tcenv1 -> tcenv

val t_bdep_solve : tcenv1 -> tcenv 

val t_bdep_simplify : tcenv1 -> tcenv

val t_extens : string option -> FApi.backward -> FApi.backward
  
val process_bdep : bdep_info -> tcenv1 -> tcenv

val process_bdepeq : bdepeq_info -> tcenv1 -> tcenv

val process_bdep_form  : pformula -> bdepvar -> tcenv1 -> tcenv

val process_bdep_eval : bdep_eval_info ->  tcenv1 -> tcenv

