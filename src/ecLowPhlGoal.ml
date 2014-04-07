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
let tc_error_notphl pf (x : bool option) =
  tc_error pf "not a HL/PHL/PRHL goal"  (* FIXME *)

(* -------------------------------------------------------------------- *)
let as_phl (kind : bool option) (dx : unit -> 'a) (pe : proofenv) =
  try dx () with DestrError _ -> tc_error_notphl pe kind

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
let pf_first_gen kind proj pe s =
  match s_first proj s with
  | None   -> tc_error pe "invalid first instruction"
  | Some x -> x

let pf_last_gen kind proj pe s =
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
let pf_as_hoareF   pe c = as_phl (Some true ) (fun () -> destr_hoareF   c) pe
let pf_as_hoareS   pe c = as_phl (Some true ) (fun () -> destr_hoareS   c) pe
let pf_as_bdhoareF pe c = as_phl (Some true ) (fun () -> destr_bdHoareF c) pe
let pf_as_bdhoareS pe c = as_phl (Some true ) (fun () -> destr_bdHoareS c) pe
let pf_as_equivF   pe c = as_phl (Some false) (fun () -> destr_equivF   c) pe
let pf_as_equivS   pe c = as_phl (Some false) (fun () -> destr_equivS   c) pe
let pf_as_eagerF   pe c = as_phl (Some false) (fun () -> destr_eagerF   c) pe

(* -------------------------------------------------------------------- *)
let tc1_as_hoareF   tc = pf_as_hoareF   !!tc (FApi.tc1_goal tc)
let tc1_as_hoareS   tc = pf_as_hoareS   !!tc (FApi.tc1_goal tc)
let tc1_as_bdhoareF tc = pf_as_bdhoareF !!tc (FApi.tc1_goal tc)
let tc1_as_bdhoareS tc = pf_as_bdhoareS !!tc (FApi.tc1_goal tc)
let tc1_as_equivF   tc = pf_as_equivF   !!tc (FApi.tc1_goal tc)
let tc1_as_equivS   tc = pf_as_equivS   !!tc (FApi.tc1_goal tc)
let tc1_as_eagerF   tc = pf_as_eagerF   !!tc (FApi.tc1_goal tc)

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
  | None   -> tc_error_notphl !!tc None
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
  | None   -> tc_error_notphl !!tc None
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
exception InvalidSplit of int * int * int

let s_split_i i s =
  let len = List.length s.s_node in
    if i < 0 || len < i then
      raise (InvalidSplit (i, 1, len));
    let (hd, tl) = EcModules.s_split (i-1) s in
    (hd, List.hd tl, List.tl tl)

let s_split i s =
  let len = List.length s.s_node in
    if i < 0 || len < i then
      raise (InvalidSplit (i, 0, len));
    EcModules.s_split i s

let s_split_o i s =
  match i with
  | None   -> ([], s.s_node)
  | Some i -> s_split i s

(* -------------------------------------------------------------------- *)
let t_hS_or_bhS_or_eS ?th ?tbh ?te tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS   _ when th  <> None -> (oget th ) tc
  | FbdHoareS _ when tbh <> None -> (oget tbh) tc
  | FequivS   _ when te  <> None -> (oget te ) tc

  | _ -> tc_error_notphl !!tc None      (* FIXME *)

let t_hF_or_bhF_or_eF ?th ?tbh ?te tc =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF   _ when th  <> None -> (oget th ) tc
  | FbdHoareF _ when tbh <> None -> (oget tbh) tc
  | FequivF   _ when te  <> None -> (oget te ) tc

  | _ -> tc_error_notphl !!tc None      (* FIXME *)

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
let lv_subst m lv f : lv_subst_t =
  match lv with
  | LvVar (pv, t) ->
    let id = id_of_pv pv m in
    (LSymbol (id, t), f), [pv,m,f_local id t]

  | LvTuple vs ->
    let ids = List.map (fun (pv,t) -> id_of_pv pv m, t) vs in
    let s   = List.map2 (fun (pv,_) (id,t) -> (pv,m,f_local id t)) vs ids in
    (LTuple ids, f), s

  | LvMap((p,tys),pv,e,ty) ->
    let id  = id_of_pv pv m in
    let set = f_op p tys (toarrow [ty; e.e_ty; f.f_ty] ty) in
    let f   = f_app set [f_pvar pv ty m; form_of_expr m e; f] ty in
    (LSymbol (id,ty), f), [pv,m,f_local id ty]

(* -------------------------------------------------------------------- *)
let mk_let_of_lv_substs env (lets, f) =
  let rec aux s lets =
    match lets with
    | [] -> PVM.subst env s f
    | ((lp, f1), toadd) :: lets ->
        let f1 = PVM.subst env s f1 in
        let s  = List.fold_left
          (fun s (pv,m,fp) -> PVM.add env pv m fp s) s toadd
        in
          f_let_simpl lp f1 (aux s lets)
  in
  if List.isempty lets then f else aux PVM.empty lets

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
  let (elts, glob) = PV.elements modi in

  (* 1. Compute the prog-vars and the globals used in [f] *)
  let fv = PV.fv env m f in

  (* 2. Split [modi] into two parts:
   *     the one used in the free-vars and the others *)
  let (uelts, nelts) = List.partition (fun (pv, _) -> PV.mem_pv env pv fv) elts in
  let (uglob, nglob) = List.partition (fun mp -> PV.mem_glob env mp fv) glob in

  (* 3. We build the related substitution *)

  (* 3.a. Add the global variables *)
  let (bd', bd, s) = generalize_subst_ env m uelts uglob in

  (* 3.b. Check that the substituion don't clash with some
          other unmodified variables *)
  List.iter (fun (pv,_) -> Mpv.check_npv env pv s) nelts;
  List.iter (fun mp -> Mpv.check_glob env mp s) nglob;

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

let t_code_transform side ?(bdhoare = false) cpos tr tx tc =
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

      | _ -> tc_error_notphl pf None    (* FIXME *)
  end

  | Some side ->
      let hyps      = FApi.tc1_hyps tc in
      let es        = tc1_as_equivS tc in
      let pre, post = es.es_pr, es.es_po in
      let me, stmt     = if side then (es.es_ml, es.es_sl) else (es.es_mr, es.es_sr) in
      let me, stmt, cs = tx (pf, hyps) cpos (pre, post) (me, stmt) in
      let concl =
        match side with
        | true  -> f_equivS_r { es with es_ml = me; es_sl = stmt; }
        | false -> f_equivS_r { es with es_mr = me; es_sr = stmt; }
      in

      FApi.xmutate1 tc (tr (Some side)) (cs @ [concl])
