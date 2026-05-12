(* -------------------------------------------------------------------- *)
open EcAst
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Structural rules for the delayed-coupling logic (paper §4.4).        *)

(* Pop: two-sided, moves the first [n] instructions of both bodies
   into the corresponding delay contexts. *)
val t_dc_pop : int -> FApi.backward

(* Pop one-sided: moves first [n] instructions of the chosen side's
   body into the corresponding delay context. *)
val t_dc_pop_side : side:[`Left | `Right] -> int -> FApi.backward

(* Push: inverse of Pop, two-sided. *)
val t_dc_push : int -> FApi.backward

(* Unpop one-sided. *)
val t_dc_push_side : side:[`Left | `Right] -> int -> FApi.backward

(* Delay axiom (two-sided): closes a goal matching
   { phi | R1 x R2 } C1 ~ C2 { phi | R1;C1 x R2;C2 }. *)
val t_dc_delay : FApi.backward

(* Delay axiom (one-sided). *)
val t_dc_delay_side : side:[`Left | `Right] -> FApi.backward

val t_dc_delay_star : side:[`Left | `Right] -> ?inv:ss_inv -> FApi.backward

val t_dc_exfalso : FApi.backward

(* Conseq: weakens pre and strengthens post by user-provided formulas. *)
val t_dc_conseq :
  pre:EcAst.ts_inv -> post:EcAst.ts_inv -> FApi.backward

(* Case: splits on a predicate [theta]. *)
val t_dc_case : form -> FApi.backward

(* Frame: adds an invariant [theta] to pre and post. The user is
   responsible for its soundness (no Write-side disjointness check yet). *)
val t_dc_frame : form -> FApi.backward

(* Indep: removes a common suffix T_i from R_i and S_i, producing a
   judgment over the "core" contexts. User provides suffix lengths
   [nl] and [nr]; the tactic checks Read/Write independence via EcPV. *)
val t_dc_indep : nl:int -> nr:int -> FApi.backward

val t_dc_trans : ts_inv -> ts_inv -> ts_inv -> ts_inv -> EcMemory.memenv -> stmt -> stmt -> stmt -> FApi.backward
