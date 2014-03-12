(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcMaps
open EcIdent
open EcPath
open EcCoreLib
open EcTypes
open EcFol
open EcBaseLogic
open EcEnv
open EcReduction

(* -------------------------------------------------------------------- *)
let set_loc loc f x =
  try f x with e -> EcLocation.locate_error loc e

let set_oloc oloc f x =
  match oloc with
  | None     -> f x
  | Some loc -> set_loc loc f x

(* -------------------------------------------------------------------- *)
let rec destruct_product hyps fp =
  let module R = EcReduction in

  match EcFol.sform_of_form fp with
  | SFquant (Lforall, (x, t), lazy f) -> Some (`Forall (x, t, f))
  | SFimp (f1, f2) -> Some (`Imp (f1, f2))
  | _ -> begin
    match R.h_red_opt R.full_red hyps fp with
    | None   -> None
    | Some f -> destruct_product hyps f
  end

(* -------------------------------------------------------------------- *)
let tacerror = EcBaseLogic.tacerror

let tacuerror = EcBaseLogic.tacuerror

let cannot_apply s1 s2 =
  tacuerror "Can not apply %s tactic:@\n %s" s1 s2
