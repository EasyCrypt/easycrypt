(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [set] transformation, resolved: the position is a
   normalized (possibly nested) code position, the value a typed
   expression. *)
type tr_set = {
  trs_at   : EcMatching.Position.nm_codepos;
  trs_name : symbol;
  trs_e    : expr;
}

type EcPlTransform.transform += TrSet of tr_set

(* -------------------------------------------------------------------- *)
(* Insert the assignment of the value to a fresh program variable. *)
let set (p : tr_set) (ctxt : tr_ctxt) (s : stmt) =
  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trs_at s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let e        = p.trs_e in
  let v        = { ov_name = Some p.trs_name; ov_type = e.e_ty } in
  let (me, id) = EcMemory.bind_fresh v ctxt.trc_me in
  (* oget cannot fail — Some in, Some out *)
  let pv       = pv_loc (EcUtils.oget id.ov_name) in
  let i        = i_asgn (LvVar (pv, e.e_ty), e) in

  { trr_me  = me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = i :: zpr.Zpr.z_tail; };
    trr_obl = []; }

let () =
  register (function
    | TrSet p -> Some (set p)
    | _ -> None)
