(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* -------------------------------------------------------------------- *)
val t_hr_exists_elim_r : ?bound:int -> backward
val t_hr_exists_elim   : backward
val t_hr_exists_intro  : inv list -> backward

(* -------------------------------------------------------------------- *)
val process_exists_intro : elim:bool -> pformula list -> backward
val process_ecall : oside -> pqsymbol * ptyannot option * pformula list -> backward
