(* -------------------------------------------------------------------- *)
open EcParsetree
open EcMatching


(* -------------------------------------------------------------------- *)
val default_start_name : string
val default_end_name   : string
val default_name       : string

(* -------------------------------------------------------------------- *)
val trans_stmt : pim_regexp -> regexp_instr

val trans_block : pim_block -> regexp_instr
