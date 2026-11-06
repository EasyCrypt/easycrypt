(* -------------------------------------------------------------------- *)
open EcAst
open EcTypes
open EcModules
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [asgn-case] transformation, resolved: the position is
   a normalized (possibly nested) code position. *)
type tr_asgn_case = {
  trac_at : EcMatching.Position.nm_codepos;
}

type EcPlTransform.transform += TrAsgnCase of tr_asgn_case

(* -------------------------------------------------------------------- *)
(* Split the assignment into one assignment per assigned variable, in
   order: the variables assigned before the last one must not be read by
   the assigned expression. *)
let asgn_case (p : tr_asgn_case) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in

  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trac_at s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let i, tl =
    match zpr.Zpr.z_tail with
    | i :: tl -> (i, tl)
    | [] -> raise (InvalidTransform "invalid code position") in

  if not (is_asgn i) then
    raise (InvalidTransform "the code position should target an assignment");

  let lv, e = destr_asgn i in

  let pvl =
    match lv with
    | LvVar _ -> PV.empty
    | LvTuple lvs ->
      let lvs = List.tl (List.rev lvs) in
      let lvs = Option.get (lv_of_list lvs) in
      EcPV.lp_write env lvs in

  let pve = EcPV.e_read env e in
  let lv  = lv_to_list lv in

  if not (EcPV.PV.indep env pvl pve) then
    raise (InvalidTransform
             "the assigned variables are read by the assigned expression");

  let e =
    match lv, e.e_node with
    | [_], _         -> [e]
    | _  , Etuple es -> es
    | _  ,_          ->
      let tys =
        match (EcEnv.Ty.hnorm e.e_ty env).ty_node with
        | Ttuple tys -> tys
        | _ -> raise (InvalidTransform "the assigned expression is not a tuple") in
      List.mapi (fun i ty -> e_proj e i ty) tys in

  if List.length lv <> List.length e then
    raise (InvalidTransform "the assigned expression is not a tuple");

  let is = List.map2 (fun pv e -> i_asgn (LvVar (pv, e.e_ty), e)) lv e in

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = is @ tl; };
    trr_obl = []; }

let () =
  register (function
    | TrAsgnCase p -> Some (asgn_case p)
    | _ -> None)
