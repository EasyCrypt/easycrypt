(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcTypes
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [alias] transformation, resolved: the position is a
   normalized (possibly nested) code position. *)
type tr_alias = {
  tral_at   : EcMatching.Position.nm_codepos;
  tral_name : symbol;
}

type EcPlTransform.transform += TrAlias of tr_alias

(* -------------------------------------------------------------------- *)
(* Store the value computed by the instruction at the position in a fresh
   program variable, then assign it to the original left-value. *)
let alias (p : tr_alias) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in

  let zpr =
    try  Zpr.zipper_of_nm_cpos p.tral_at s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let i, tl =
    match zpr.Zpr.z_tail with
    | i :: tl -> (i, tl)
    | [] -> raise (InvalidTransform "invalid code position") in

  let dopv ty =
    let id       = { ov_name = Some p.tral_name; ov_type = ty; } in
    let (me, id) = EcMemory.bind_fresh id ctxt.trc_me in
    (* oget cannot fail — Some in, Some out *)
    let pv       = pv_loc (EcUtils.oget id.ov_name) in
    me, pv in

  let me, is =
    match i.i_node with
    | Sasgn (lv, e) ->
        let ty       = e.e_ty in
        let (me, pv) = dopv ty in
        (me, [i_asgn (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])

    | Srnd (lv, e) ->
        let ty       = EcFol.proj_distr_ty env e.e_ty in
        let (me, pv) = dopv ty in
        (me, [i_rnd (LvVar (pv, ty), e); i_asgn (lv, e_var pv ty)])

    | Scall (Some lv, f, args) ->
        let ty       = (EcEnv.Fun.by_xpath f env).f_sig.fs_ret in
        let (me, pv) = dopv ty in
        (me, [i_call (Some (LvVar (pv, ty)), f, args); i_asgn (lv, e_var pv ty)])

    | _ ->
        raise (InvalidTransform
                 "cannot create an alias for that kind of instruction")
  in

  { trr_me  = me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = is @ tl; };
    trr_obl = []; }

let () =
  register (function
    | TrAlias p -> Some (alias p)
    | _ -> None)
