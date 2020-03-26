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
open EcTypes
open EcModules
open EcMemory
open EcFol
open EcEnv
open EcPV
open EcCoreGoal

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
type lv_subst_t = (lpattern * form) * (prog_var * memory * form) list

(* -------------------------------------------------------------------- *)
type hlform = [`Any | `Pred | `Stmt]

type hlkind = [
  | `Hoare  of hlform
  | `PHoare of hlform
  | `Equiv  of hlform
  | `Eager
]

and hlkinds = hlkind list

let hlkinds_Xhl_r (form : hlform) : hlkinds =
  [`Hoare form; `PHoare form; `Equiv form]

let hlkinds_Xhl = hlkinds_Xhl_r `Any

let hlkinds_all : hlkinds =
  [`Hoare `Any; `PHoare `Any; `Equiv `Any; `Eager]

(* -------------------------------------------------------------------- *)
let tc_error_noXhl ?(kinds : hlkinds option) pf =
  let string_of_form =
    function `Pred -> "[F]" | `Stmt -> "[S]" | `Any -> "" in

  let rec string_of_kind kind =
    let kind, fm =
      match kind with
      | `Hoare  fm -> ("hoare" , fm)
      | `PHoare fm -> ("phoare", fm)
      | `Equiv  fm -> ("equiv" , fm)
      | `Eager     -> ("eager" , `Any)
    in
      Printf.sprintf "%s%s" kind (fm |> string_of_form)
  in

  tc_error_lazy pf (fun fmt ->
    Format.fprintf fmt "expecting a goal of the form: %s"
      (String.concat ", " (List.map string_of_kind (odfl [] kinds))))

(* -------------------------------------------------------------------- *)
let as_phl (kind : hlkind) (dx : unit -> 'a) (pe : proofenv) =
  try dx () with DestrError _ -> tc_error_noXhl ~kinds:[kind] pe

(* -------------------------------------------------------------------- *)
let s_first proj s =
  match s.s_node with
  | []     -> None
  | i :: r ->
      try  let i = proj i in Some (i, stmt r)
      with Not_found -> None

let s_last proj s =
  match List.rev s.s_node with
  | []     -> None
  | i :: r ->
      try  let i = proj i in Some (i, stmt (List.rev r))
      with Not_found -> None

(* -------------------------------------------------------------------- *)
let pf_first_gen _kind proj pe s =
  match s_first proj s with
  | None   -> tc_error pe "invalid first instruction"
  | Some x -> x

let pf_last_gen _kind proj pe s =
  match s_last proj s with
  | None   -> tc_error pe "invalid last instruction"
  | Some x -> x

(* -------------------------------------------------------------------- *)
let pf_first_asgn   pe st = pf_first_gen  "asgn"   destr_asgn   pe st
let pf_first_rnd    pe st = pf_first_gen  "rnd"    destr_rnd    pe st
let pf_first_call   pe st = pf_first_gen  "call"   destr_call   pe st
let pf_first_if     pe st = pf_first_gen  "if"     destr_if     pe st
let pf_first_while  pe st = pf_first_gen  "while"  destr_while  pe st
let pf_first_assert pe st = pf_first_gen  "assert" destr_assert pe st

(* -------------------------------------------------------------------- *)
let pf_last_asgn   pe st = pf_last_gen  "asgn"   destr_asgn   pe st
let pf_last_rnd    pe st = pf_last_gen  "rnd"    destr_rnd    pe st
let pf_last_call   pe st = pf_last_gen  "call"   destr_call   pe st
let pf_last_if     pe st = pf_last_gen  "if"     destr_if     pe st
let pf_last_while  pe st = pf_last_gen  "while"  destr_while  pe st
let pf_last_assert pe st = pf_last_gen  "assert" destr_assert pe st

(* -------------------------------------------------------------------- *)
let tc1_first_asgn   tc st = pf_first_asgn   !!tc st
let tc1_first_rnd    tc st = pf_first_rnd    !!tc st
let tc1_first_call   tc st = pf_first_call   !!tc st
let tc1_first_if     tc st = pf_first_if     !!tc st
let tc1_first_while  tc st = pf_first_while  !!tc st
let tc1_first_assert tc st = pf_first_assert !!tc st

(* -------------------------------------------------------------------- *)
let tc1_last_asgn   tc st = pf_last_asgn   !!tc st
let tc1_last_rnd    tc st = pf_last_rnd    !!tc st
let tc1_last_call   tc st = pf_last_call   !!tc st
let tc1_last_if     tc st = pf_last_if     !!tc st
let tc1_last_while  tc st = pf_last_while  !!tc st
let tc1_last_assert tc st = pf_last_assert !!tc st

(* -------------------------------------------------------------------- *)
(* TODO: use in change pos *)

let pf_pos_last_gen msg test pe s =
  match List.orindex test s.s_node with
  | None -> tc_error pe "can not find the last %s instruction" msg
  | Some i -> i

let pf_pos_last_asgn   pe s = pf_pos_last_gen "asgn"   is_asgn   pe s
let pf_pos_last_rnd    pe s = pf_pos_last_gen "rnd"    is_rnd    pe s
let pf_pos_last_call   pe s = pf_pos_last_gen "call"   is_call   pe s
let pf_pos_last_if     pe s = pf_pos_last_gen "if"     is_if     pe s
let pf_pos_last_while  pe s = pf_pos_last_gen "while"  is_while  pe s
let pf_pos_last_assert pe s = pf_pos_last_gen "assert" is_assert pe s


let tc1_pos_last_asgn   tc s = pf_pos_last_asgn   !!tc s
let tc1_pos_last_rnd    tc s = pf_pos_last_rnd    !!tc s
let tc1_pos_last_call   tc s = pf_pos_last_call   !!tc s
let tc1_pos_last_if     tc s = pf_pos_last_if     !!tc s
let tc1_pos_last_while  tc s = pf_pos_last_while  !!tc s
let tc1_pos_last_assert tc s = pf_pos_last_assert !!tc s

(* -------------------------------------------------------------------- *)
let pf_as_hoareF   pe c = as_phl (`Hoare  `Pred) (fun () -> destr_hoareF   c) pe
let pf_as_hoareS   pe c = as_phl (`Hoare  `Stmt) (fun () -> destr_hoareS   c) pe
let pf_as_bdhoareF pe c = as_phl (`PHoare `Pred) (fun () -> destr_bdHoareF c) pe
let pf_as_bdhoareS pe c = as_phl (`PHoare `Stmt) (fun () -> destr_bdHoareS c) pe
let pf_as_equivF   pe c = as_phl (`Equiv  `Pred) (fun () -> destr_equivF   c) pe
let pf_as_equivS   pe c = as_phl (`Equiv  `Stmt) (fun () -> destr_equivS   c) pe
let pf_as_eagerF   pe c = as_phl `Eager          (fun () -> destr_eagerF   c) pe

(* -------------------------------------------------------------------- *)
let tc1_as_hoareF   tc = pf_as_hoareF   !!tc (FApi.tc1_goal tc)
let tc1_as_hoareS   tc = pf_as_hoareS   !!tc (FApi.tc1_goal tc)
let tc1_as_bdhoareF tc = pf_as_bdhoareF !!tc (FApi.tc1_goal tc)
let tc1_as_bdhoareS tc = pf_as_bdhoareS !!tc (FApi.tc1_goal tc)
let tc1_as_equivF   tc = pf_as_equivF   !!tc (FApi.tc1_goal tc)
let tc1_as_equivS   tc = pf_as_equivS   !!tc (FApi.tc1_goal tc)
let tc1_as_eagerF   tc = pf_as_eagerF   !!tc (FApi.tc1_goal tc)

(* -------------------------------------------------------------------- *)
let tc1_get_stmt side tc =
  let concl = FApi.tc1_goal tc in
  match side, concl.f_node with
  | None, FhoareS hs -> hs.hs_s
  | None, FbdHoareS hs -> hs.bhs_s
  | Some _ , (FhoareS _ | FbdHoareS _) ->
      tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt] !!tc
  | Some `Left, FequivS es   -> es.es_sl
  | Some `Right, FequivS es  -> es.es_sr
  | None, FequivS _ ->
      tc_error_noXhl ~kinds:[`Equiv `Stmt] !!tc
  | _            ->
      tc_error_noXhl ~kinds:(hlkinds_Xhl_r `Stmt) !!tc

(* -------------------------------------------------------------------- *)
let get_pre f =
  match f.f_node with
  | FhoareF hf   -> Some (hf.hf_pr )
  | FhoareS hs   -> Some (hs.hs_pr )
  | FbdHoareF hf -> Some (hf.bhf_pr)
  | FbdHoareS hs -> Some (hs.bhs_pr)
  | FequivF ef   -> Some (ef.ef_pr )
  | FequivS es   -> Some (es.es_pr )
  | _            -> None

let tc1_get_pre tc =
  match get_pre (FApi.tc1_goal tc) with
  | None   -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc
  | Some f -> f

(* -------------------------------------------------------------------- *)
let get_post f =
  match f.f_node with
  | FhoareF hf   -> Some (hf.hf_po )
  | FhoareS hs   -> Some (hs.hs_po )
  | FbdHoareF hf -> Some (hf.bhf_po)
  | FbdHoareS hs -> Some (hs.bhs_po)
  | FequivF ef   -> Some (ef.ef_po )
  | FequivS es   -> Some (es.es_po )
  | _            -> None

let tc1_get_post tc =
  match get_post (FApi.tc1_goal tc) with
  | None   -> tc_error_noXhl ~kinds:hlkinds_Xhl !!tc
  | Some f -> f

(* -------------------------------------------------------------------- *)
let set_pre ~pre f =
  match f.f_node with
 | FhoareF hf   -> f_hoareF pre hf.hf_f hf.hf_po
 | FhoareS hs   -> f_hoareS_r { hs with hs_pr = pre }
 | FbdHoareF hf -> f_bdHoareF pre hf.bhf_f hf.bhf_po hf.bhf_cmp hf.bhf_bd
 | FbdHoareS hs -> f_bdHoareS_r { hs with bhs_pr = pre }
 | FequivF ef   -> f_equivF pre ef.ef_fl ef.ef_fr ef.ef_po
 | FequivS es   -> f_equivS_r { es with es_pr = pre }
 | _            -> assert false

(* -------------------------------------------------------------------- *)
exception InvalidSplit of codepos1

let s_split i s =
  let module Zpr = EcMatching.Zipper in
  try  Zpr.split_at_cpos1 i s
  with Zpr.InvalidCPos -> raise (InvalidSplit i)

let s_split_i i s =
  let module Zpr = EcMatching.Zipper in
  try  Zpr.find_by_cpos1 ~rev:false i s
  with Zpr.InvalidCPos -> raise (InvalidSplit i)

let o_split ?rev i s =
  let module Zpr = EcMatching.Zipper in
  try  Zpr.may_split_at_cpos1 ?rev i s
  with Zpr.InvalidCPos -> raise (InvalidSplit (oget i))

(* -------------------------------------------------------------------- *)
let t_hS_or_bhS_or_eS ?th ?tbh ?te tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ when EcUtils.is_some th  -> (oget th ) tc
  | FbdHoareS _ when EcUtils.is_some tbh -> (oget tbh) tc
  | FequivS   _ when EcUtils.is_some te  -> (oget te ) tc

  | _ ->
    let kinds = List.flatten [
         if EcUtils.is_some th  then [`Hoare  `Stmt] else [];
         if EcUtils.is_some tbh then [`PHoare `Stmt] else [];
         if EcUtils.is_some te  then [`Equiv  `Stmt] else []]

    in tc_error_noXhl ~kinds !!tc

let t_hF_or_bhF_or_eF ?th ?tbh ?te ?teg tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF   _ when EcUtils.is_some th  -> (oget th ) tc
  | FbdHoareF _ when EcUtils.is_some tbh -> (oget tbh) tc
  | FequivF   _ when EcUtils.is_some te  -> (oget te ) tc
  | FeagerF   _ when EcUtils.is_some teg -> (oget teg) tc

  | _ ->
    let kinds = List.flatten [
         if EcUtils.is_some th  then [`Hoare  `Pred] else [];
         if EcUtils.is_some tbh then [`PHoare `Pred] else [];
         if EcUtils.is_some te  then [`Equiv  `Pred] else [];
         if EcUtils.is_some teg then [`Eager       ] else []]

    in tc_error_noXhl ~kinds !!tc

(* -------------------------------------------------------------------- *)
let tag_sym_with_side name m =
  if      EcIdent.id_equal m EcFol.mleft  then (name ^ "_L")
  else if EcIdent.id_equal m EcFol.mright then (name ^ "_R")
  else    name

(* -------------------------------------------------------------------- *)
let id_of_pv pv m =
  let id = EcPath.basename pv.pv_name.EcPath.x_sub in
  let id = tag_sym_with_side id m in
    EcIdent.create id

(* -------------------------------------------------------------------- *)
let id_of_mp mp m =
  let name =
    match mp.EcPath.m_top with
    | `Local id -> EcIdent.name id
    | _ -> assert false
  in
    EcIdent.create (tag_sym_with_side name m)

(* -------------------------------------------------------------------- *)
let fresh_pv me v =
  let rec for_idx idx =
    let x = Printf.sprintf "%s%d" v.v_name idx in
      if EcMemory.is_bound x me then
        for_idx (idx+1)
      else
        (EcMemory.bind x v.v_type me, x)
  in
    if EcMemory.is_bound v.v_name me then
      for_idx 0
    else
      (EcMemory.bind v.v_name v.v_type me, v.v_name)

(* -------------------------------------------------------------------- *)
let lv_subst m lv f = lv, m, f

(* -------------------------------------------------------------------- *)
let mk_let_of_lv_substs_nolet env (lets, f) =
  if List.is_empty lets then f
  else
    let s =
      List.fold_left (fun s (lv,m,f1) ->
        let f1 = PVM.subst env s f1 in
        match lv, f1.f_node with
        | LvVar (pv,_), _ -> PVM.add env pv m f1 s
        | LvTuple vs, Ftuple fs ->
          List.fold_left2 (fun s (pv,_) f -> PVM.add env pv m f s) s vs fs
        | LvTuple vs, _ ->
          List.fold_lefti
            (fun s i (pv,ty) -> PVM.add env pv m (f_proj f i ty) s)
            s vs
        )  PVM.empty lets in
    PVM.subst env s f

let add_lv_subst env lv m s =
  match lv with
  | LvVar (pv,t) ->
    let id = id_of_pv pv m in
    let s = PVM.add env pv m (f_local id t) s in
    LSymbol(id, t), s

  | LvTuple pvs ->
    let s, ids =
      List.map_fold (fun s (pv,t) ->
        let id = id_of_pv pv m in
        let s = PVM.add env pv m (f_local id t) s in
        s, (id,t)) s pvs in
    LTuple ids, s

let mk_let_of_lv_substs_let env (lets, f) =
  if List.is_empty lets then f
  else
    let accu,s =
      List.fold_left (fun (accu,s) (lv,m,f1) ->
        let f1 = PVM.subst env s f1 in
        let lv, s = add_lv_subst env lv m s in
        (lv,f1)::accu, s) ([],PVM.empty) lets in
    (* accu is the sequence of let in reverse order *)
    let f = PVM.subst env s f in
    (* compute the fv *)
    let _, fvlets =
      List.fold_left (fun (fv2,lets) (lp,f1 as lpf) ->
        let fv = EcIdent.fv_diff fv2 (lp_fv lp) in
        let fv = EcIdent.fv_union (f_fv f1) fv in
        fv, (lpf,fv2)::lets) (f.f_fv,[]) accu in
    (* fvlets is the sequence of let in the right order *)
    (* build the lets and perform the substitution/simplification *)
    let add_id fv (accu,s) (id,ty) f1 =
      match EcIdent.Mid.find_opt id fv with
      | None   -> (accu, s)
      | Some i ->
        if   i = 1 || can_subst f1
        then accu, Fsubst.f_bind_local s id f1
        else (LSymbol(id,ty), f1)::accu, s in

    let rlets, s =
      List.fold_left (fun (rlets,s as accus) ((lp,f1),fv) ->
        let f1 = Fsubst.f_subst s f1 in
        match lp, f1.f_node with
        | LRecord _, _ -> assert false
        | LSymbol idt, _ -> add_id fv accus idt f1
        | LTuple ids, Ftuple fs -> List.fold_left2 (add_id fv) accus ids fs
        | LTuple ids, _ ->
          let used =
            List.fold_left (fun u (id, _) ->
              match u, EcIdent.Mid.find_opt id fv with
              | Some i1, Some i2 -> Some (i1+i2)
              | None, i | i, None -> i) None ids in
          match used with
          | None -> accus
          | Some i ->
            let accus, fx =
              if i = 1 || can_subst f1 then accus, f1
              else
                let x = EcIdent.create "tpl" in
                let ty = ttuple (List.map snd ids) in
                let lpx = LSymbol(x,ty) in
                let fx = f_local x ty in
                ((lpx,f1)::rlets,s), fx in
            List.fold_lefti (fun accus i (_,ty as idt) ->
              add_id fv accus idt (f_proj fx i ty)) accus ids)
        ([],Fsubst.f_subst_id) fvlets in
    List.fold_left (fun f2 (lp,f1) -> f_let lp f1 f2) (Fsubst.f_subst s f) rlets


let mk_let_of_lv_substs ?(uselet=true) env letsf =
  if uselet then mk_let_of_lv_substs_let env letsf
  else mk_let_of_lv_substs_nolet env letsf

(* -------------------------------------------------------------------- *)
let subst_form_lv env m lv t f =
  let lets = lv_subst m lv t in
  mk_let_of_lv_substs env ([lets], f)

(* -------------------------------------------------------------------- *)
(* Remark: m is only used to create fresh name, id_of_pv *)
let generalize_subst_ env m uelts uglob =
  let create (pv, ty) = id_of_pv pv m, GTty ty in
  let b = List.map create uelts in
  let s =
    List.fold_left2
      (fun s (pv, ty) (id, _) ->
        Mpv.add env pv (f_local id ty) s)
      Mpv.empty uelts b
  in
  let create mp = id_of_mp mp m, GTty (tglob mp) in
  let b' = List.map create uglob in
  let s  =
    List.fold_left2
      (fun s mp (id, _) ->
        Mpv.add_glob env mp (f_local id (tglob mp)) s)
      s uglob b'
  in
    (b', b, s)

let generalize_mod_ env m modi f =
  let (melts, mglob) = PV.ntr_elements modi in

  (* 1. Compute the prog-vars and the globals used in [f] *)
  let fv = PV.fv env m f in
  let felts, fglob = PV.ntr_elements fv in

  (* 2. Split [modi] into two parts:
   *    the one used in the free-vars and the others *)
  let (uelts, nelts) = List.partition (fun (pv, _) -> PV.mem_pv env pv modi) felts in
  let (uglob, nglob) = List.partition (fun mp -> PV.mem_glob env mp modi) fglob in

  (* 3. We build the related substitution *)

  (* 3.a. Add the global variables *)

  let (bd', bd, s ) = generalize_subst_ env m uelts uglob in
   (* 3.b. Check that the modify variables does not clash with
           the variables not generalized *)
  let restrs =
    List.fold_left (fun r mp ->
      let restr = NormMp.get_restr env mp in
      EcPath.Mm.add mp restr r) EcPath.Mm.empty mglob in
  List.iter (fun (npv,_) ->
    if is_glob npv then
      let check1 mp restr =  Mpv.check_npv_mp env npv mp restr in
      EcPath.Mm.iter check1 restrs) nelts;
  List.iter (fun mp ->
    let restr = NormMp.get_restr env mp in
    let check (npv,_) =
      if is_glob npv then
        Mpv.check_npv_mp env npv mp restr in
    List.iter check melts;
    let check mp' restr' = Mpv.check_mp_mp env mp restr mp' restr' in
    EcPath.Mm.iter check restrs) nglob;

  (* 3.c. Perform the substitution *)
  let s = PVM.of_mpv s m in
  let f = PVM.subst env s f in
  f_forall_simpl (bd'@bd) f, (bd', uglob), (bd, uelts)

let generalize_subst env m uelts uglob =
  let (b',b,f) = generalize_subst_ env m uelts uglob in
  b'@b, f

let generalize_mod env m modi f =
  let res, _, _ = generalize_mod_ env m modi f in
  res

(* -------------------------------------------------------------------- *)
let abstract_info env f1 =
  let f   = EcEnv.NormMp.norm_xfun env f1 in
  let top = EcPath.m_functor f.EcPath.x_top in
  let def = EcEnv.Fun.by_xpath f env in
  let oi  =
    match def.f_def with
    | FBabs oi -> oi
    | _ ->
      let ppe = EcPrinting.PPEnv.ofenv env in
        if EcPath.x_equal f1 f then
          EcCoreGoal.tacuerror
            "The function %a should be abstract"
            (EcPrinting.pp_funname ppe) f1
        else
          EcCoreGoal.tacuerror
            "The function %a, which reduces to %a, should be abstract"
            (EcPrinting.pp_funname ppe) f1
            (EcPrinting.pp_funname ppe) f
  in
    (top, f, oi, def.f_sig)

(* -------------------------------------------------------------------- *)
let abstract_info2 env fl' fr' =
  let (topl, fl, oil, sigl) = abstract_info env fl' in
  let (topr, fr, oir, sigr) = abstract_info env fr' in
  let fl1 = EcPath.xpath topl fl.EcPath.x_sub in
  let fr1 = EcPath.xpath topr fr.EcPath.x_sub in
    if not (EcPath.x_equal fl1 fr1) then begin
      let ppe = EcPrinting.PPEnv.ofenv env in
        EcCoreGoal.tacuerror
          "function %a reduces to %a and %a reduces to %a, %a and %a should be equal"
          (EcPrinting.pp_funname ppe) fl'
          (EcPrinting.pp_funname ppe) fl1
          (EcPrinting.pp_funname ppe) fr'
          (EcPrinting.pp_funname ppe) fr1
          (EcPrinting.pp_funname ppe) fl1
          (EcPrinting.pp_funname ppe) fr1
    end;
    ((topl, fl, oil, sigl), (topr, fr, oir, sigr))

(* -------------------------------------------------------------------- *)
type code_txenv = proofenv * LDecl.hyps

type 'a code_tx =
     code_txenv -> 'a -> form pair -> memenv * stmt
   -> memenv * stmt * form list

type 'a zip_t =
     code_txenv -> form pair -> memenv -> Zpr.zipper
  -> memenv * Zpr.zipper * form list

let t_fold f (cenv : code_txenv) (cpos : codepos) (_ : form * form) (state, s) =
  try
    let (me, f) = Zpr.fold cenv cpos f state s in
      ((me, f, []) : memenv * _ * form list)
  with Zpr.InvalidCPos -> tc_error (fst cenv) "invalid code position"

let t_zip f (cenv : code_txenv) (cpos : codepos) (prpo : form * form) (state, s) =
  try
    let (me, zpr, gs) = f cenv prpo state (Zpr.zipper_of_cpos cpos s) in
      ((me, Zpr.zip zpr, gs) : memenv * _ * form list)
  with Zpr.InvalidCPos -> tc_error (fst cenv) "invalid code position"

let t_code_transform (side : oside) ?(bdhoare = false) cpos tr tx tc =
  let pf = FApi.tc1_penv tc in

  match side with
  | None -> begin
      let (hyps, concl) = FApi.tc1_flat tc in

      match concl.f_node with
      | FhoareS hoare ->
          let pr, po = hoare.hs_pr, hoare.hs_po in
          let (me, stmt, cs) = tx (pf, hyps) cpos (pr, po) (hoare.hs_m, hoare.hs_s) in
          let concl = f_hoareS_r { hoare with hs_m = me; hs_s = stmt; } in
          FApi.xmutate1 tc (tr None) (cs @ [concl])

      | FbdHoareS bhs when bdhoare ->
          let pr, po = bhs.bhs_pr, bhs.bhs_po in
          let (me, stmt, cs) = tx (pf, hyps) cpos (pr, po) (bhs.bhs_m, bhs.bhs_s) in
          let concl = f_bdHoareS_r { bhs with bhs_m = me; bhs_s = stmt; } in
          FApi.xmutate1 tc (tr None) (cs @ [concl])

      | _ ->
        match bdhoare with
        | true  -> tc_error_noXhl ~kinds:[`Hoare `Stmt; `PHoare `Stmt] pf
        | false -> tc_error_noXhl ~kinds:[`Hoare `Stmt] pf
  end

  | Some side ->
      let hyps      = FApi.tc1_hyps tc in
      let es        = tc1_as_equivS tc in
      let pre, post = es.es_pr, es.es_po in
      let me, stmt     =
        match side with
        | `Left  -> (es.es_ml, es.es_sl)
        | `Right -> (es.es_mr, es.es_sr) in
      let me, stmt, cs = tx (pf, hyps) cpos (pre, post) (me, stmt) in
      let concl =
        match side with
        | `Left  -> f_equivS_r { es with es_ml = me; es_sl = stmt; }
        | `Right -> f_equivS_r { es with es_mr = me; es_sr = stmt; }
      in

      FApi.xmutate1 tc (tr (Some side)) (cs @ [concl])
