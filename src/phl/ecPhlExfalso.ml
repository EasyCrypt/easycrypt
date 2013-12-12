(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl
open EcPhlTauto

(* -------------------------------------------------------------------- *)
let t_exfalso g =
  let concl = get_concl g in
    t_or
      (t_core_exfalso)
      (t_seq_subgoal
         (EcPhlConseq.t_conseq f_false (get_post concl))
         [t_id None; t_logic_trivial; t_core_exfalso ])
      g
