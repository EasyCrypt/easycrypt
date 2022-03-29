(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_hoare_swap   : int -> int -> int -> backward
val t_choare_swap  : int -> int -> int -> backward
val t_bdhoare_swap : int -> int -> int -> backward
val t_equiv_swap   : side -> int -> int -> int -> backward

(* -------------------------------------------------------------------- *)
val process_swap : (oside * swap_kind) located list -> backward

(* -------------------------------------------------------------------- *)
val process_interleave : interleave_info located -> backward
