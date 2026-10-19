(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal
open EcAst

(* -------------------------------------------------------------------- *)
(* Procedure calls in the delayed-coupling logic (paper §5). All the
   stacks handed over to a callee must only mention global variables. *)

(* Two-sided Call: the last instruction of each body is a call. The
   specification is an F-level dcoupl judgement whose delay contexts
   are [tl]/[tr] and whose continuations are those of the goal.       *)
val t_dc_call :
     fpre:ts_inv -> fpost:ts_inv
  -> tl:stmt -> tr:stmt
  -> FApi.backward

(* One-sided Call with a lossless Hoare specification. The chosen
   side's stacks must be unchanged ([S = R]) and independent from the
   callee.                                                             *)
val t_dc_call1 :
     side:side -> fpre:ss_inv -> fpost:ss_inv
  -> FApi.backward

(* Abs: abstract procedures (adversaries) at F-level, with an
   invariant; produces the two conseq goals then one dcoupl goal per
   oracle, all carrying the (unchanged) stacks.                        *)
val t_dc_fun_abs : ts_inv -> FApi.backward

(* [proc I]: Abs on abstract procedures, unfolding otherwise. *)
val t_dc_fun : ts_inv -> FApi.backward

(* Call from an axiom (F-level dcoupl or lossless bdhoare). *)
val t_dc_call_ax : oside -> form -> FApi.backward

(* -------------------------------------------------------------------- *)
val process_dc_fun_abs : pformula -> FApi.backward

val process_dc_call :
     oside
  -> dc_call_info gppterm
  -> (pstmt * pstmt) option
  -> FApi.backward
