(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcModules
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the [simplify-if] transformation, resolved: the position
   is a normalized (possibly nested) code position. *)
type tr_simplify_if = {
  trsi_at : EcMatching.Position.nm_codepos;
}

type EcPlTransform.transform += TrSimplifyIf of tr_simplify_if

(* -------------------------------------------------------------------- *)
(* The single assignment computing the final values of the variables
   written by the branches [s1] / [s2] (assignments only) of
   [if e then s1 else s2]; no instruction when they write nothing. *)
let simplify_if (env : EcEnv.env) (e : expr) (s1 : stmt) (s2 : stmt) =
  let mod1 = s_write env s1 in
  let mod2 = s_write env s2 in
  let modv, modg = PV.elements (PV.union mod1 mod2) in

  if not (List.is_empty modg) then
    raise (InvalidTransform "the branches modify global variables");

  if List.is_empty modv then [] else

  let upd (m : (expr, unit) Mpv.t) (x : prog_var) (e : expr) =
    Mpv.add env x e (Mpv.remove env x m)
  in

  let init =
    List.fold_left
      (fun m (x, ty) -> Mpv.add env x (e_var x ty) m)
      Mpv.empty modv
  in

  let transform_v m (x, ty) =
    let x' = EcIdent.create (symbol_of_pv x) in
    upd m x (e_local x' ty), (x', ty) in

  let transform_lv m lv =
    match lv with
    | LvVar (x, ty) ->
        let m, (x', ty) = transform_v m (x, ty) in
        m, LSymbol (x', ty)
    | LvTuple xs ->
        let m, xs' = List.map_fold transform_v m xs in
        m, LTuple xs' in

  let transform_i m i =
    let lv, e = destr_asgn i in
    let e = Mpv.esubst env m e in
    let m, lp = transform_lv m lv in
    m, (lp, e) in

  let transform_s (s : stmt) =
    List.map_fold transform_i init s.s_node in

  let m1, bd1 = transform_s s1 in
  let m2, bd2 = transform_s s2 in

  let es =
    let e_if (x, ty) =
      let ex = e_var x ty in
      e_if e (Mpv.esubst env m1 ex) (Mpv.esubst env m2 ex) in
    e_tuple (List.map e_if modv) in

  let add_binding bd es =
    List.fold_right (fun (lp, e) es -> e_let lp e es) bd es in

  let es = add_binding bd1 (add_binding bd2 es) in
  [i_asgn (oget (lv_of_list modv), es)]

(* -------------------------------------------------------------------- *)
(* Replace the conditional at the position by a single assignment. *)
let simplify_if_tr (p : tr_simplify_if) (ctxt : tr_ctxt) (s : stmt) =
  let zpr =
    try  Zpr.zipper_of_nm_cpos p.trsi_at s
    with EcMatching.Position.InvalidCPos ->
      raise (InvalidTransform "invalid code position") in

  let i, tl =
    match zpr.Zpr.z_tail with
    | i :: tl -> (i, tl)
    | [] -> raise (InvalidTransform "invalid code position") in

  let is =
    match i.i_node with
    | Sif (e, s1, s2) ->
        if not (List.for_all is_asgn s1.s_node) then
          raise (InvalidTransform
            "the then branch contains intruction that are not assignments");
        if not (List.for_all is_asgn s2.s_node) then
          raise (InvalidTransform
            "the else branch contains intruction that are not assignments");
        simplify_if ctxt.trc_env e s1 s2
    | _ ->
        raise (InvalidTransform
          "the given position does not correspond to an if instruction")
  in

  { trr_me  = ctxt.trc_me;
    trr_s   = Zpr.zip { zpr with Zpr.z_tail = is @ tl; };
    trr_obl = []; }

let () =
  register (function
    | TrSimplifyIf p -> Some (simplify_if_tr p)
    | _ -> None)
