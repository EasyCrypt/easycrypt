(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcMaps
open EcLocation
open EcPath
open EcAst
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
  | IPmatch of s_pat list

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
    | Smatch (e, bs)     -> i_match  (esubst e, List.Smart.map (snd_map ssubst) bs)
    | Sassert e          -> i_assert (esubst e)
    | Sabstract _        -> i

  and issubst m (is : instr list) =
    List.Smart.map (isubst m) is

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
      let _params =
        let named_arg ov =
          match ov.ov_name with
          | None   -> assert false
          | Some v -> { v_name = v; v_type = ov.ov_type }
        in List.map named_arg f.f_sig.fs_anames
      in
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

      let body = LowSubst.ssubst subst fdef.f_body in

      let me, resasgn =
        match fdef.f_ret, lv with
        | None, _ -> me , []
        | Some _, None -> me, []
        | Some r, Some (LvTuple lvs) when not use_tuple ->
          let r = LowSubst.esubst subst r in
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
          let r = LowSubst.esubst subst r in
          me, [i_asgn (lv, r)] in

      me, prelude @ body.s_node @ resasgn in

    let rec inline_i me ip i =
      match ip, i.i_node with
      | IPpat, Scall (lv, p, args) ->
          inline1 me lv p args
      | IPif (sp1, sp2), Sif (e, s1, s2) ->
          let me, s1 = inline_s me sp1 s1.s_node in
          let me, s2 = inline_s me sp2 s2.s_node in
          me, [i_if (e, stmt s1, stmt s2)]
      | IPwhile sp, Swhile (e, s) ->
          let me, s = inline_s me sp s.s_node in
          me, [i_while (e, stmt s)]
      | IPmatch sps, Smatch (e, bs) ->
          let me, bs = List.fold_left_map (fun me (sp, (xs, s)) ->
              let me, s = inline_s me sp s.s_node in (me, (xs, stmt s)))
            me (List.combine sps bs)
          in me, [i_match (e, bs)]

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
  let hs           = tc1_as_hoareS tc in
  let (_,mt), stmt = LowInternal.inline ~use_tuple tc hs.hs_m sp hs.hs_s in
  let concl        = f_hoareS mt (hs_pr hs) stmt (hs_po hs) in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_ehoare_r ~use_tuple sp tc =
  let ehs          = tc1_as_ehoareS tc in
  let (_,mt), stmt = LowInternal.inline ~use_tuple tc ehs.ehs_m sp ehs.ehs_s in
  let concl        = f_eHoareS mt (ehs_pr ehs) stmt (ehs_po ehs) in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_bdhoare_r ~use_tuple sp tc =
  let bhs           = tc1_as_bdhoareS tc in
  let (_, mt), stmt = LowInternal.inline ~use_tuple tc bhs.bhs_m sp bhs.bhs_s in
  let concl         = f_bdHoareS mt (bhs_pr bhs) stmt (bhs_po bhs) bhs.bhs_cmp (bhs_bd bhs) in


  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_equiv_r ~use_tuple side sp tc =
  let es = tc1_as_equivS tc in
  let concl =
    match side with
    | `Left  ->
        let ((_,mt), stmt) = LowInternal.inline ~use_tuple tc es.es_ml sp es.es_sl in
          f_equivS mt (snd es.es_mr) (es_pr es) stmt es.es_sr (es_po es)
    | `Right ->
        let ((_,mt), stmt) = LowInternal.inline ~use_tuple tc es.es_mr sp es.es_sr in
          f_equivS (snd es.es_ml) mt (es_pr es) es.es_sl stmt (es_po es)
  in

  FApi.xmutate1 tc `Inline [concl]

(* -------------------------------------------------------------------- *)
let t_inline_hoare ~use_tuple =
  FApi.t_low1 "hoare-inline"   (t_inline_hoare_r ~use_tuple)
let t_inline_ehoare  ~use_tuple =
  FApi.t_low1 "hoare-inline"   (t_inline_ehoare_r ~use_tuple)
let t_inline_bdhoare ~use_tuple =
  FApi.t_low1 "bdhoare-inline" (t_inline_bdhoare_r ~use_tuple)
let t_inline_equiv ~use_tuple =
  FApi.t_low2 "equiv-inline"   (t_inline_equiv_r ~use_tuple)

(* -------------------------------------------------------------------- *)
module HiInternal = struct
  (* ------------------------------------------------------------------ *)
  let pat_all cond s =

    let test = EcPath.Hx.memo 0 cond in

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

      | Smatch (_, bs) ->
          let sps = List.map (fun (_, b) -> aux_s 0 b.s_node) bs in
          if   List.for_all List.is_empty sps
          then None
          else Some (IPmatch sps)

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
      | Zp.ZMatch (_, sp, mpi) ->
        let prebr  = List.map (fun _ -> []) mpi.prebr  in
        let postbr = List.map (fun _ -> []) mpi.postbr in
        aux_s (IPmatch (prebr @ aout :: postbr)) sp

    and aux_s aout ((sl, _), ip) =
      aux_i [(List.length sl, aout)] ip

    in fun (p : Zp.spath) -> aux_s IPpat p

  (* ------------------------------------------------------------------ *)
  let pat_of_codepos env pos stmt =
    let module Zp = EcMatching.Zipper in

    let zip = Zp.zipper_of_cpos env pos stmt in
    match zip.Zp.z_tail with
    | { i_node = Scall _ } :: tl ->
         pat_of_spath ((zip.Zp.z_head, tl), zip.Zp.z_path)
    | _ -> raise Zp.InvalidCPos
end

(* -------------------------------------------------------------------- *)
let rec process_inline_all ~use_tuple side cond tc =
  let concl = FApi.tc1_goal tc in

  match concl.f_node, side with
  | FequivS _, None ->
      FApi.t_seq
        (process_inline_all ~use_tuple (Some `Left ) cond)
        (process_inline_all ~use_tuple (Some `Right) cond)
        tc

  | FequivS es, Some b -> begin
      let st = sideif b es.es_sl es.es_sr in
      match HiInternal.pat_all cond st with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_equiv ~use_tuple b sp)
                (process_inline_all ~use_tuple  side cond)
                tc
  end

  | FhoareS hs, None -> begin
      match HiInternal.pat_all cond hs.hs_s with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_hoare ~use_tuple sp)
                (process_inline_all ~use_tuple side cond)
                tc
  end


  | FeHoareS hs, None -> begin
      match HiInternal.pat_all cond hs.ehs_s with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_ehoare ~use_tuple sp)
                (process_inline_all ~use_tuple side cond)
                tc
  end

  | FbdHoareS bhs, None -> begin
      match HiInternal.pat_all cond bhs.bhs_s with
      | [] -> t_id tc
      | sp -> FApi.t_seq
                (t_inline_bdhoare ~use_tuple sp)
                (process_inline_all ~use_tuple side cond)
                tc
  end

  | _, _ -> tc_error !!tc "invalid arguments"

(* -------------------------------------------------------------------- *)
let process_inline_occs ~use_tuple side cond occs tc =
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
  let env = FApi.tc1_env tc in
  let concl = FApi.tc1_goal tc in
  let pos = EcLowPhlGoal.tc1_process_codepos tc (side, pos) in

  try
    match concl.f_node, side with
    | FequivS es, Some b ->
        let st = sideif b es.es_sl es.es_sr in
        let sp = HiInternal.pat_of_codepos env pos st in
        t_inline_equiv ~use_tuple b sp tc

    | FhoareS hs, None ->
        let sp = HiInternal.pat_of_codepos env pos hs.hs_s in
        t_inline_hoare ~use_tuple sp tc

    | FbdHoareS bhs, None ->
        let sp = HiInternal.pat_of_codepos env pos bhs.bhs_s in
        t_inline_bdhoare ~use_tuple sp tc

    | _, _ -> tc_error !!tc "invalid arguments"

  with EcMatching.Zipper.InvalidCPos ->
    tc_error !!tc "invalid position"

(* -------------------------------------------------------------------- *)
let process_info tc infos =
  let env = FApi.tc1_env tc in
  let doit (dir, pat) =
    let pat =
      match pat with
      | `InlineXpath f ->
        let f = EcTyping.trans_gamepath env f in
        `InlineXpath (EcEnv.NormMp.norm_xfun env f)
      | `InlinePat (pm, (sub, f)) ->
        let pm =
          List.rev_map (fun (p, o) ->
            if o <> None then tc_error !!tc ~loc:(loc p) "can not provide functor arguments";
            unloc p) (unloc pm) in
        let sub = List.rev_map unloc sub in
        let f = omap unloc f in
        `InlinePat(pm, sub, f)
      | `InlineAll -> `InlineAll in
     (dir, pat) in
  List.map doit infos


(* -------------------------------------------------------------------- *)
let test_match pm sub fx f =

  let rec test_path ids p =
    match ids, p.p_node with
    | [], _ -> true
    | [id], EcPath.Psymbol id' -> EcSymbols.sym_equal id id'
    | id::ids, EcPath.Pqname(p, id') -> EcSymbols.sym_equal id id' && test_path ids p
    | _, _ -> false
    in

  begin match fx with None -> true | Some sym -> EcSymbols.sym_equal sym f.x_sub end
  && match f.x_top.m_top with
  | `Local a ->
    sub = [] &&
    begin match pm with
    | [] -> true
    | [id] -> EcSymbols.sym_equal id (EcIdent.name a)
    | _ -> false
    end

  | `Concrete (p, sp) -> ofold (fun sp b -> b && test_path sub sp) (test_path pm p) sp


let test_pat for_occ env infos f =
  let fn = EcEnv.NormMp.norm_xfun env f in

  let test_pat1 all pat =
    match pat with
    | `InlineXpath fn' -> EcPath.x_equal fn fn'
    | `InlinePat (pm, sub, fx) -> test_match pm sub fx f
    | `InlineAll ->
      all ||
      match (EcEnv.Fun.by_xpath fn env).f_def with
      | FBdef _ -> true | _ -> false in

  let rec aux b infos =
    match infos with
    | [] -> b
    | (`UNION, pat) :: infos -> aux (b || test_pat1 for_occ pat) infos
    | (`DIFF, pat) :: infos -> aux (b && not(test_pat1 true pat)) infos in

  aux false infos

(* -------------------------------------------------------------------- *)
let process_inline infos tc =
  let use_tuple use =
    odfl true (omap (function `UseTuple b -> b) use) in
  match infos with
  | `ByName (side, use, (infos, occs)) ->
    let infos = process_info tc infos in
    let infos = if infos = [] then [`UNION, `InlineAll] else infos in
    let env = FApi.tc1_env tc in
    let use_tuple = use_tuple use in
    begin match occs with
    | None      -> process_inline_all ~use_tuple side (test_pat false env infos) tc
    | Some occs -> process_inline_occs ~use_tuple side (test_pat true env infos) occs tc
    end

  | `CodePos (side, use, pos) ->
    process_inline_codepos ~use_tuple:(use_tuple use) side pos tc
