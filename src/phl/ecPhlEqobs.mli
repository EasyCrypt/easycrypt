(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcParsetree
open EcAst
open EcMatching.Position
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
type sim_info = {
  sim_pos  : codepos1 pair option;
  sim_hint : (xpath option * xpath option * EcPV.Mpv2.t) list * form option;
  sim_eqs  : EcPV.Mpv2.t option;
}

val empty_sim_info : sim_info

(* -------------------------------------------------------------------- *)
val t_eqobs_in : crushmode option -> sim_info -> backward
val process_eqobs_in : crushmode option -> psim_info -> backward
