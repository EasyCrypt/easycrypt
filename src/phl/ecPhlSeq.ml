(* -------------------------------------------------------------------- *)
open EcParsetree
open EcAst

open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The [seq] rules live, one module per logic, in [rules/<logic>/]: each
   owns its parameter records, pure subgoal builder, recheckable proof-node,
   checker and elaboration. This module only keeps the legacy positional
   entry points (adapters onto those rules, so external callers and this
   module's interface are unchanged) and the logic-agnostic dispatcher. *)

(* -------------------------------------------------------------------- *)
let t_hoare_seq i phi =
  EcHoareSeq.(t_hoare_seq { hsr_at = i; hsr_mid = phi })

let t_ehoare_seq i phi =
  EcEHoareSeq.(t_ehoare_seq { ehsr_at = i; ehsr_mid = phi })

(* Adapts onto the derived form: rule + discharge of the non-modification
   subgoal. *)
let t_bdhoare_seq i (phi, pR, f1, f2, g1, g2) =
  EcBdHoareSeq.(t_bdhoare_seq_full
    { bsr_at = i; bsr_phi = phi; bsr_r = pR;
      bsr_f1 = f1; bsr_f2 = f2; bsr_g1 = g1; bsr_g2 = g2; })

let t_equiv_seq (i, j) phi =
  EcEquivSeq.(t_equiv_seq { esr_at = (i, j); esr_mid = phi })

let t_equiv_seq_onesided = EcEquivSeq.t_equiv_seq_onesided

(* -------------------------------------------------------------------- *)
(* Dispatch on the goal kind only; each logic owns its surface-syntax
   handling and takes the whole [seq_info] record. *)
let process_seq (info : seq_info) (tc : tcenv1) =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ -> EcHoareSeq.process_hoare_seq     info tc
  | FeHoareS  _ -> EcEHoareSeq.process_ehoare_seq   info tc
  | FbdHoareS _ -> EcBdHoareSeq.process_bdhoare_seq info tc
  | FequivS   _ -> EcEquivSeq.process_equiv_seq     info tc
  | _ ->
      match info.seqi_bd with
      | PSeqNone -> tc_error !!tc "invalid `position' parameter"
      | _        -> tc_error !!tc "optional bound parameter not supported"
