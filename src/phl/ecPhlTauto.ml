(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic
open EcFol
open EcCorePhl
(* -------------------------------------------------------------------- *)
class rn_hoare_true =
object
  inherit xrule "[hl] hoare-true"
end

let rn_hoare_true =
  RN_xtd (new rn_hoare_true :> xrule)

let t_hoare_true g = 
  let concl = get_concl g in
  match concl.f_node with
  | FhoareF hf when f_equal hf.hf_po f_true ->
    prove_goal_by [] rn_hoare_true g   
  | FhoareS hs when f_equal hs.hs_po f_true ->
    prove_goal_by [] rn_hoare_true g    
  | _ -> tacuerror "the conclusion should have the form hoare[_ : _ ==> true]"

(* -------------------------------------------------------------------- *)
class rn_hl_exfalso = object
  inherit xrule "[hl] exfalso"
end

let rn_hl_exfalso = RN_xtd (new rn_hl_exfalso)

let t_core_exfalso g =
  let concl = get_concl g in
  let pre   = get_pre concl in
    if pre <> f_false then
      cannot_apply "exfalso" "pre-condition is not `false'";
    prove_goal_by [] rn_hl_exfalso g


