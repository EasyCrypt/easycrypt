(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcMaps
open EcTypes
open EcModules
open EcFol
open EcEnv
open EcPV

open EcCoreGoal
open EcLowGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
type i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat

and s_pat = (int * i_pat) list

(* -------------------------------------------------------------------- *)
module LowSubst = struct
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
    | Sassert e          -> i_assert (esubst e)
    | Sabstract _        -> i

  and issubst m (is : instr list) =
    List.map (isubst m) is

  and ssubst m (st : stmt) =
    stmt (issubst m st.s_node)
end

(* --------------------------------------------------------------------- *)
module LowInternal = struct
  let inline ~use_tuple tc me sp s =
    let hyps = FApi.tc1_hyps tc in
    let env  = LDecl.toenv hyps in

    let inline1 me lv p args =
      let p = EcEnv.NormMp.norm_xfun env p in
      let f = EcEnv.Fun.by_xpath p env in
      let fdef =
        match f.f_def with
        | FBdef def -> def
        | _ -> begin
            tc_error_lazy !!tc (fun fmt ->
              let ppe = EcPrinting.PPEnv.ofenv env in
                Format.fprintf fmt
                  "abstract function `%a' cannot be inlined"
                  (EcPrinting.pp_funname ppe) p)
        end
      in
      let params =
        match f.f_sig.fs_anames with
        | None -> [{ v_name = "arg"; v_type = f.f_sig.fs_arg; }]
        | Some lv -> lv in
      let me, anames =
        List.map_fold fresh_pv me params in
      let me, lnames =
        List.map_fold fresh_pv me fdef.f_locals in
      let subst =
        let for1 mx v x =
          PVMap.add
            (pv_loc p v.v_name)
            (pv_loc (EcMemory.xpath me) x)
            mx
        in
        let mx = PVMap.create env in
        let mx = List.fold_left2 for1 mx params anames in
        let mx = List.fold_left2 for1 mx fdef.f_locals lnames in

        mx
      in

      let prelude =
        let newpv =
          List.map2
            (fun v newx -> pv_loc (EcMemory.xpath me) newx, v.v_type)
            params anames in
        if List.length newpv = List.length args then
          List.map2 (fun npv e -> i_asgn (LvVar npv, e)) newpv args
        else
          match newpv with
          | [x] -> [i_asgn(LvVar x, e_tuple args)]
          | _   -> [i_asgn(LvTuple newpv, e_tuple args)]
      in

      let body = LowSubst.ssubst subst fdef.f_body in

      let me, resasgn =
        match fdef.f_ret, lv with
        | None, _ -> me , []
        | Some _, None -> me, []
        | Some r, Some (LvTuple lvs) when not use_tuple ->
          let r = LowSubst.esubst subst r in
          let me, auxs =
            let doit me (x, ty) =
              let v = {v_name = symbol_of_pv x; v_type = ty} in
              let me, pv = fresh_pv me v in
              let pv = pv_loc (EcMemory.xpath me) pv in
              me, (pv, ty) in
            List.map_fold doit me lvs in
          let s1 =
            let doit i auxi = i_asgn(LvVar auxi, e_proj_simpl r i (snd auxi)) in
            List.mapi doit auxs in
          let s2 =
            List.map2 (fun lv (pv, ty) -> i_asgn(LvVar lv, e_var pv ty)) lvs auxs in
          me, s1 @ s2
        | Some r, Some lv ->
          let r = LowSubst.esubst subst r in
          me, [i_asgn (lv, r)] in

      me, prelude @ body.s_node @ resasgn in

    let rec inline_i me ip i =
      match ip, i.i_node with
      | IPpat, Scall (lv, p, args) ->
          inline1 me lv p args
      | IPif(sp1, sp2), Sif(e,s1,s2) ->
          let me,s1 = inline_s me sp1 s1.s_node in
          let me,s2 = inline_s me sp2 s2.s_node in
          me, [i_if (e, stmt s1, stmt s2)]
      | IPwhile sp, Swhile(e,s) ->
          let me, s = inline_s me sp s.s_node in
          me, [i_while(e,stmt s)]
      | _, _ -> assert false (* FIXME error message *)

    and inline_s me sp s =
      match sp with
      | [] -> me, s
      | (toskip, ip)::sp ->
        let r, i, s = List.pivot_at toskip s in
        let me, si = inline_i me ip i in
        let me, s  = inline_s me sp s in
        (me, List.rev_append r (si @ s))

    in

    snd_map stmt (inline_s me sp s.s_node)
end

(* -------------------------------------------------------------------- *)
let t_inline_hoare_r ~use_tuple sp tc =
  let hoare      = tc1_as_hoareS tc in
  let (me, stmt) = LowInternal.inline ~use_tuple tc hoare.hs_m sp hoare.hs_s in
  let concl      = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_bdhoare_r ~use_tuple sp tc =
  let hoare      = tc1_as_bdhoareS tc in
  let (me, stmt) = LowInternal.inline ~use_tuple tc hoare.bhs_m sp hoare.bhs_s in
  let concl      = f_bdHoareS_r { hoare with bhs_m = me; bhs_s = stmt; } in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_equiv_r ~use_tuple side sp tc =
  let equiv = tc1_as_equivS tc in
  let concl =
    match side with
    | `Left  ->
        let (me, stmt) = LowInternal.inline ~use_tuple tc equiv.es_ml sp equiv.es_sl in
          f_equivS_r { equiv with es_ml = me; es_sl = stmt; }
    | `Right ->
        let (me, stmt) = LowInternal.inline ~use_tuple tc equiv.es_mr sp equiv.es_sr in
          f_equivS_r { equiv with es_mr = me; es_sr = stmt; }
  in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_hoare   ~use_tuple = FApi.t_low1 "hoare-inline"   (t_inline_hoare_r ~use_tuple)
let t_inline_bdhoare ~use_tuple = FApi.t_low1 "bdhoare-inline" (t_inline_bdhoare_r ~use_tuple)
let t_inline_equiv   ~use_tuple = FApi.t_low2 "equiv-inline"   (t_inline_equiv_r ~use_tuple)

(* -------------------------------------------------------------------- *)
module HiInternal = struct
  (* ------------------------------------------------------------------ *)
  let pat_all env fs s =
    let test f =
      let is_defined = function FBdef _ -> true | _ -> false in

      match fs with
      | Some fs -> EcPath.Sx.mem (EcEnv.NormMp.norm_xfun env f) fs
      | None    ->
          let f = EcEnv.NormMp.norm_xfun env f in
          let f = EcEnv.Fun.by_xpath f env in
          is_defined f.f_def
    in

    let test = EcPath.Hx.memo 0 test in

    let rec aux_i i =
      match i.i_node with
      | Scall (_, f, _) ->
          if test f then Some IPpat else None

      | Sif (_, s1, s2) ->
          let sp1 = aux_s 0 s1.s_node in
          let sp2 = aux_s 0 s2.s_node in
          if   List.is_empty sp1 && List.is_empty sp2
          then None
          else Some (IPif (sp1, sp2))

      | Swhile (_, s) ->
          let sp = aux_s 0 s.s_node in
          if List.is_empty sp then None else Some (IPwhile (sp))

      | _ -> None

    and aux_s n s =
      match s with
      | []   -> []
      | i::s ->
        match aux_i i with
        | None    -> aux_s (n+1) s
        | Some ip -> (n,ip) :: aux_s 0 s
    in
      aux_s 0 s.s_node

  (* ------------------------------------------------------------------ *)
  let pat_of_occs cond occs s =
    let occs = ref occs in

    let rec aux_i occ i =
      match i.i_node with
      | Scall (_,f,_) ->
        if cond f then
          let occ = 1 + occ in
          if Sint.mem occ !occs then begin
            occs := Sint.remove occ !occs;
            occ, Some IPpat
          end else occ, None
        else occ, None

      | Sif (_, s1, s2) ->
        let occ, sp1 = aux_s occ 0 s1.s_node in
        let occ, sp2 = aux_s occ 0 s2.s_node in
        let ip = if sp1 = [] && sp2 = [] then None else Some (IPif (sp1, sp2)) in
        occ, ip

      | Swhile (_, s) ->
        let occ, sp = aux_s occ 0 s.s_node in
        let ip = if sp = [] then None else Some(IPwhile sp) in
        occ, ip

      | _ -> occ, None

    and aux_s occ n s =
      match s with
      | []   -> occ, []
      | i::s ->
        match aux_i occ i with
        | occ, Some ip ->
          let occ, sp = aux_s occ 0 s in
          occ, (n, ip) :: sp
        | occ, None -> aux_s occ (n+1) s in

    let sp = snd (aux_s 0 0 s.s_node) in

    assert (Sint.is_empty !occs); sp    (* FIXME error message *)

  (* ------------------------------------------------------------------ *)
  let pat_of_spath =
    let module Zp = EcMatching.Zipper in

    let rec aux_i aout ip =
      match ip with
      | Zp.ZTop -> aout
      | Zp.ZWhile  (_, sp)    -> aux_s (IPwhile aout) sp
      | Zp.ZIfThen (_, sp, _) -> aux_s (IPif (aout, [])) sp
      | Zp.ZIfElse (_, _, sp) -> aux_s (IPif ([], aout)) sp

    and aux_s aout ((sl, _), ip) =
      aux_i [(List.length sl, aout)] ip

    in fun (p : Zp.spath) -> aux_s IPpat p

  (* ------------------------------------------------------------------ *)
  let pat_of_codepos pos stmt =
    let module Zp = EcMatching.Zipper in

    let zip = Zp.zipper_of_cpos pos stmt in
    match zip.Zp.z_tail with
    | { i_node = Scall _ } :: tl ->
         pat_of_spath ((zip.Zp.z_head, tl), zip.Zp.z_path)
    | _ -> raise Zp.InvalidCPos
end

(* -------------------------------------------------------------------- *)
let rec process_inline_all ~use_tuple side fs tc =
  let env, _, concl = FApi.tc1_eflat tc in

  match concl.f_node, side with
  | FequivS _, None ->
      FApi.t_seq
        (process_inline_all ~use_tuple (Some `Left ) fs)
        (process_inline_all ~use_tuple (Some `Right) fs)
        tc

  | FequivS es, Some b -> begin
      let st = sideif b es.es_sl es.es_sr in
      match HiInternal.pat_all env fs st with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_equiv ~use_tuple b sp)
                (process_inline_all ~use_tuple  side fs)
                tc
  end

  | FhoareS hs, None -> begin
      match HiInternal.pat_all env fs hs.hs_s with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_hoare ~use_tuple sp)
                (process_inline_all ~use_tuple side fs)
                tc
  end

  | FbdHoareS bhs, None -> begin
      match HiInternal.pat_all env fs bhs.bhs_s with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_bdhoare ~use_tuple sp)
                (process_inline_all ~use_tuple side fs)
                tc
  end

  | _, _ -> tc_error !!tc "invalid arguments"

(* -------------------------------------------------------------------- *)
let process_inline_occs ~use_tuple side fs occs tc =
  let env = FApi.tc1_env tc in
  let cond =
    if   EcPath.Sx.is_empty fs
    then fun _ -> true
    else fun f -> EcPath.Sx.mem (EcEnv.NormMp.norm_xfun env f) fs in
  let occs  = Sint.of_list occs in
  let concl = FApi.tc1_goal tc in

  match concl.f_node, side with
  | FequivS es, Some b ->
      let st = sideif b es.es_sl es.es_sr in
      let sp = HiInternal.pat_of_occs cond occs st in
        t_inline_equiv ~use_tuple b sp tc

  | FhoareS hs, None ->
      let sp = HiInternal.pat_of_occs cond occs hs.hs_s in
        t_inline_hoare ~use_tuple sp tc

  | FbdHoareS bhs, None ->
      let sp = HiInternal.pat_of_occs cond occs bhs.bhs_s in
        t_inline_bdhoare ~use_tuple sp tc

  | _, _ -> tc_error !!tc "invalid arguments"

(* -------------------------------------------------------------------- *)
let process_inline_codepos ~use_tuple side pos tc =
  let concl = FApi.tc1_goal tc in

  try
    match concl.f_node, side with
    | FequivS es, Some b ->
        let st = sideif b es.es_sl es.es_sr in
        let sp = HiInternal.pat_of_codepos pos st in
        t_inline_equiv ~use_tuple b sp tc

    | FhoareS hs, None ->
        let sp = HiInternal.pat_of_codepos pos hs.hs_s in
        t_inline_hoare ~use_tuple sp tc

    | FbdHoareS bhs, None ->
        let sp = HiInternal.pat_of_codepos pos bhs.bhs_s in
        t_inline_bdhoare ~use_tuple sp tc

    | _, _ -> tc_error !!tc "invalid arguments"

  with EcMatching.Zipper.InvalidCPos ->
    tc_error !!tc "invalid position"

(* -------------------------------------------------------------------- *)
let process_inline infos tc =
  let use_tuple use =
    odfl true (omap (function `UseTuple b -> b) use) in

  match infos with
  | `ByName (side, use, (fs, occs)) -> begin
      let env = FApi.tc1_env tc in
      let use_tuple = use_tuple use in
      let fs  =
        List.fold_left (fun fs f ->
          let f = EcTyping.trans_gamepath env f in
            EcPath.Sx.add (EcEnv.NormMp.norm_xfun env f) fs)
          EcPath.Sx.empty fs
      in
        match occs with
        | None      -> process_inline_all ~use_tuple side (Some fs) tc
        | Some occs -> process_inline_occs ~use_tuple side fs occs tc
    end

  | `CodePos (side, use, pos) ->
       process_inline_codepos ~use_tuple:(use_tuple use) side pos tc

  | `All (side, use) -> process_inline_all ~use_tuple:(use_tuple use) side None tc
