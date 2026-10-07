(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcTypes
open EcModules
open EcPV
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the [inline] transformation, resolved: the calls to
   inline are selected by a pattern of integer offsets. *)
type i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat
  | IPmatch of s_pat list

and s_pat = (int * i_pat) list

type tr_inline = {
  tri_pat       : s_pat;
  tri_use_tuple : bool;
}

type EcPlTransform.transform += TrInline of tr_inline

(* -------------------------------------------------------------------- *)
(* Renaming of program variables in a statement. *)
module Subst = struct
  let pvsubst m pv =
    odfl pv (PVMap.find pv m)

  let rec esubst m e =
    match e.e_node with
    | Evar pv -> e_var (pvsubst m pv) e.e_ty
    | _ -> EcTypes.e_map (fun ty -> ty) (esubst m) e

  let lvsubst m lv =
    match lv with
    | LvVar   (pv, ty)       -> LvVar (pvsubst m pv, ty)
    | LvTuple pvs            -> LvTuple (List.map (fst_map (pvsubst m)) pvs)

  let rec isubst m (i : instr) =
    let esubst = esubst m in
    let ssubst = ssubst m in

    match i.i_node with
    | Sasgn  (lv, e)     -> i_asgn   (lvsubst m lv, esubst e)
    | Srnd   (lv, e)     -> i_rnd    (lvsubst m lv, esubst e)
    | Scall  (lv, f, es) -> i_call   (lv |> omap (lvsubst m), f, List.map esubst es)
    | Sif    (c, s1, s2) -> i_if     (esubst c, ssubst s1, ssubst s2)
    | Swhile (e, stmt)   -> i_while  (esubst e, ssubst stmt)
    | Smatch (e, bs)     -> i_match  (esubst e, List.Smart.map (snd_map ssubst) bs)
    | Sraise e           -> i_raise  (esubst e)
    | Sabstract _        -> i

  and issubst m (is : instr list) =
    List.Smart.map (isubst m) is

  and ssubst m (st : stmt) =
    stmt (issubst m st.s_node)
end

(* -------------------------------------------------------------------- *)
let invalid_pattern () =
  raise (InvalidTransform "invalid inlining pattern")

(* Inline the call [lv <- p(args)]: returns the extended memory and the
   inlined instructions. [inloop] holds iff the call is in a loop body. *)
let inline1 ~use_tuple ~inloop env me lv p args =
  let p = EcEnv.NormMp.norm_xfun env p in
  let f = EcEnv.Fun.by_xpath p env in
  let fdef =
    match f.f_def with
    | FBdef def -> def
    | _ ->
        let ppe = EcPrinting.PPEnv.ofenv env in
        raise (InvalidTransform
                 (Format.asprintf "abstract function `%a' cannot be inlined"
                    (EcPrinting.pp_funname ppe) p)) in

  (* The callee's parameters and locals become fresh variables of the
   * caller. Outside of a loop, these variables are never written
   * before the inlined body, and hence hold, as the callee's locals,
   * an unconstrained initial value. Inside a loop body, they are
   * shared by all iterations and start with the value left by the
   * previous one, whereas a call starts with fresh locals. Inlining
   * is then only sound if the callee never reads a local before
   * writing it (parameters are written by the prelude): the inlined
   * code does not depend on the initial value of these variables. *)
  if inloop then begin
    let uninit = EcCoreModules.get_uninit_read_of_fun f in
    if not (EcSymbols.Ssym.is_empty uninit) then
      let ppe = EcPrinting.PPEnv.ofenv env in
      raise (InvalidTransform
               (Format.asprintf
                  "function `%a' cannot be inlined inside a loop: \
                   it may use the uninitialized local variable(s): %a"
                  (EcPrinting.pp_funname ppe) p
                  (EcPrinting.pp_list ", " EcSymbols.pp_symbol)
                  (EcSymbols.Ssym.elements uninit)))
  end;

  let me, anames = EcMemory.bindall_fresh f.f_sig.fs_anames me in
  let me, lnames = EcMemory.bindall_fresh (List.map ovar_of_var fdef.f_locals) me in
  let subst =
    let for1 mx v x =
      PVMap.add (pv_loc (oget v.ov_name)) (pv_loc (oget x.ov_name)) mx
    in
    let mx = PVMap.create env in
    let mx = List.fold_left2 for1 mx f.f_sig.fs_anames anames in
    let mx = List.fold_left2 for1 mx (List.map ovar_of_var fdef.f_locals) lnames in
    mx
  in

  let prelude =
    let newpv = List.map (fun x -> pv_loc (oget x.ov_name), x.ov_type) anames in
    if List.length newpv = List.length args then
      List.map2 (fun npv e -> i_asgn (LvVar npv, e)) newpv args
    else
      match newpv with
      | [x] -> [i_asgn(LvVar x, e_tuple args)]
      | _   -> [i_asgn(LvTuple newpv, e_tuple args)]
  in

  let body = Subst.ssubst subst fdef.f_body in

  let me, resasgn =
    match fdef.f_ret, lv with
    | None, _ -> me , []
    | Some _, None -> me, []
    | Some r, Some (LvTuple lvs) when not use_tuple ->
      let r = Subst.esubst subst r in
      let vlvs =
        List.map (fun (x,ty) -> { ov_name = Some (symbol_of_pv x); ov_type = ty}) lvs in
      let me, auxs = EcMemory.bindall_fresh vlvs me in
      let auxs = List.map (fun v -> pv_loc (oget v.ov_name), v.ov_type) auxs in
      let s1 =
        let doit i auxi = i_asgn(LvVar auxi, e_proj_simpl r i (snd auxi)) in
        List.mapi doit auxs in
      let s2 =
        List.map2 (fun lv (pv, ty) -> i_asgn(LvVar lv, e_var pv ty)) lvs auxs in
      me, s1 @ s2

    | Some r, Some lv ->
      let r = Subst.esubst subst r in
      me, [i_asgn (lv, r)] in

  me, prelude @ body.s_node @ resasgn

(* -------------------------------------------------------------------- *)
(* Inline, in program order, the calls selected by the pattern. *)
let inline (p : tr_inline) (ctxt : tr_ctxt) (s : stmt) =
  let use_tuple = p.tri_use_tuple in

  let rec inline_i ~inloop me ip i =
    match ip, i.i_node with
    | IPpat, Scall (lv, p, args) ->
        inline1 ~use_tuple ~inloop ctxt.trc_env me lv p args
    | IPif (sp1, sp2), Sif (e, s1, s2) ->
        let me, s1 = inline_s ~inloop me sp1 s1.s_node in
        let me, s2 = inline_s ~inloop me sp2 s2.s_node in
        me, [i_if (e, stmt s1, stmt s2)]
    | IPwhile sp, Swhile (e, s) ->
        let me, s = inline_s ~inloop:true me sp s.s_node in
        me, [i_while (e, stmt s)]
    | IPmatch sps, Smatch (e, bs) when List.length sps = List.length bs ->
        let me, bs = List.fold_left_map (fun me (sp, (xs, s)) ->
            let me, s = inline_s ~inloop me sp s.s_node in (me, (xs, stmt s)))
          me (List.combine sps bs)
        in me, [i_match (e, bs)]

    | _, _ -> invalid_pattern ()

  and inline_s ~inloop me sp s =
    match sp with
    | [] -> me, s
    | (toskip, ip)::sp ->
      let r, i, s =
        try  List.pivot_at toskip s
        with Not_found | Invalid_argument _ -> invalid_pattern () in
      let me, si = inline_i ~inloop me ip i in
      let me, s  = inline_s ~inloop me sp s in
      (me, List.rev_append r (si @ s))

  in

  let me, s = inline_s ~inloop:false ctxt.trc_me p.tri_pat s.s_node in
  { trr_me = me; trr_s = stmt s; trr_obl = []; }

let () =
  register (function
    | TrInline p -> Some (inline p)
    | _ -> None)
