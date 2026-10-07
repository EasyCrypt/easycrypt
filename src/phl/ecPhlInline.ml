(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUtils
open EcMaps
open EcLocation
open EcPath
open EcAst
open EcModules

open EcCoreGoal
open EcLowGoal

(* -------------------------------------------------------------------- *)
(* The [inline] tactic is derived: it resolves the calls to inline to a
   pattern of integer offsets and applies the [inline] program
   transformation ([EcTrInline]) through the transformation rule of the
   goal's logic ([Ec<Logic>Transform]; equiv: one side at a time). The
   derived tactic is the same in every logic, so this module holds it
   directly (one line per logic), with the resolution and the
   elaboration. *)

(* -------------------------------------------------------------------- *)
type i_pat = EcTrInline.i_pat =
  | IPpat
  | IPif    of s_pat pair
  | IPwhile of s_pat
  | IPmatch of s_pat list

and s_pat = (int * i_pat) list

(* -------------------------------------------------------------------- *)
let tr_inline ~use_tuple sp =
  EcTrInline.TrInline { tri_pat = sp; tri_use_tuple = use_tuple }

let t_inline_hoare ~use_tuple sp =
  EcHoareTransform.t_hoare_transform { htr_tr = tr_inline ~use_tuple sp }

let t_inline_ehoare ~use_tuple sp =
  EcEHoareTransform.t_ehoare_transform { ehtr_tr = tr_inline ~use_tuple sp }

let t_inline_bdhoare ~use_tuple sp =
  EcBdHoareTransform.t_bdhoare_transform { btr_tr = tr_inline ~use_tuple sp }

let t_inline_equiv ~use_tuple side sp =
  EcEquivTransform.t_equiv_transform
    { etr_side = side; etr_tr = tr_inline ~use_tuple sp }

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
    | _ -> raise EcMatching.Position.InvalidCPos
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

  with EcMatching.Position.InvalidCPos ->
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
