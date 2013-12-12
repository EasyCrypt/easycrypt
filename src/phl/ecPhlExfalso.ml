(* -------------------------------------------------------------------- *)
open EcFol
open EcBaseLogic
open EcLogic
open EcCorePhl

(* -------------------------------------------------------------------- *)
class rn_hl_exfalso = object
  inherit xrule "[hl] exfalso"
end

let rn_hl_exfalso = RN_xtd (new rn_hl_exfalso)

(* -------------------------------------------------------------------- *)
let t_core_exfalso g =
  let concl = get_concl g in
  let pre   = get_pre concl in
    if pre <> f_false then
      cannot_apply "exfalso" "pre-condition is not `false'";
    prove_goal_by [] rn_hl_exfalso g

(* -------------------------------------------------------------------- *)
let t_exfalso g =
  let concl = get_concl g in
    t_or
      (t_core_exfalso)
      (t_seq_subgoal
         (EcPhlConseq.t_conseq f_false (get_post concl))
         [t_id None; t_logic_trivial; t_core_exfalso ])
      g
