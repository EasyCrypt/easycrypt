(* -------------------------------------------------------------------- *)
open EcLocation
open EcParsetree
open EcMatching.Position
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type swap_kind = {
  interval : (codepos1 * codepos1 option) option;
  offset   : codeoffset1;
}

(* -------------------------------------------------------------------- *)
val t_swap : oside -> swap_kind -> backward

(* -------------------------------------------------------------------- *)
val process_swap : (oside * pswap_kind) located list -> backward

(* -------------------------------------------------------------------- *)
val process_interleave : interleave_info located -> backward
