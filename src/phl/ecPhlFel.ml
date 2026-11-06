(* -------------------------------------------------------------------- *)
(* The [fel] rule lives in [rules/bdhoare/]. This module only keeps the
   legacy entry points. *)

(* -------------------------------------------------------------------- *)
let t_failure_event at_pos cntr ash q f_event pred_specs inv tc =
  EcBdHoareFel.(t_bdhoare_fel
    { felr_at    = at_pos;
      felr_cntr  = cntr;
      felr_asg   = ash;
      felr_q     = q;
      felr_event = f_event;
      felr_specs = pred_specs;
      felr_inv   = inv; }) tc

(* -------------------------------------------------------------------- *)
let process_fel = EcBdHoareFel.process_bdhoare_fel
