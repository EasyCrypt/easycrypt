(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcCoreGoal.FApi
open EcMatching.Position

(* -------------------------------------------------------------------- *)
val t_fission    : oside -> codepos -> int * (int * int) -> backward
val t_fusion     : oside -> codepos -> int * (int * int) -> backward
val t_unroll     : oside -> codepos -> backward
val t_splitwhile : expr -> oside -> codepos -> backward

(* -------------------------------------------------------------------- *)
type fission_t    = oside * pcodepos * (int * (int * int))
type fusion_t     = oside * pcodepos * (int * (int * int))
type unroll_t     = oside * pcodepos * bool
type splitwhile_t = pexpr * oside * pcodepos

val process_unroll_for : oside -> pcodepos -> backward
val process_fission    : fission_t -> backward
val process_fusion     : fusion_t -> backward
val process_unroll     : unroll_t -> backward
val process_splitwhile : splitwhile_t -> backward
