(* -------------------------------------------------------------------- *)
open EcBaseLogic
open EcLogic
open EcFol

(* -------------------------------------------------------------------- *)
class rn_hoare_true =
object
  inherit xrule "[hl] hoare-true"
end

let rn_hoare_true =
  RN_xtd (new rn_hoare_true :> xrule)

(* -------------------------------------------------------------------- *)
let t_hoare_true g = 
  let concl = get_concl g in
  match concl.f_node with
  | FhoareF hf when f_equal hf.hf_po f_true ->
    prove_goal_by [] rn_hoare_true g   
  | FhoareS hs when f_equal hs.hs_po f_true ->
    prove_goal_by [] rn_hoare_true g    
  | _ -> tacuerror "the conclusion should have the form hoare[_ : _ ==> true]"


(* -------------------------------------------------------------------- *)
let t_trivial = 
  let subtc = 
    t_lor [t_hoare_true;
           EcPhlExfalso.t_core_exfalso;   
           EcPhlPr.t_prbounded false;
           EcPhlSkip.t_skip]
  in
    t_try
      (t_lseq [t_try t_assumption;
               t_progress (t_id None);
               t_try t_assumption; 
               subtc; t_logic_trivial; t_fail])
