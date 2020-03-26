(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcIdent
open EcSymbols
open EcPath
open EcTypes
open EcFol
open EcEnv
open EcMatching
open EcReduction
open EcCoreGoal
open EcBaseLogic
open EcProofTerm

module EP  = EcParsetree
module ER  = EcReduction
module TTC = EcProofTyping
module LG  = EcCoreLib.CI_Logic
module PT  = EcProofTerm

(* -------------------------------------------------------------------- *)
let (@!) (t1 : FApi.backward) (t2 : FApi.backward) =
  FApi.t_seq t1 t2

let (@+) (t : FApi.backward) (ts : FApi.backward list) =
  FApi.t_seqsub t ts

let (@>) (t1 : FApi.backward) (t2 : FApi.backward) =
  fun tc -> FApi.t_last t1 (t2 tc)

let (@~) (t : FApi.backward) (tt : FApi.tactical) =
  fun tc -> tt (t tc)

let (@!+) (tt : FApi.tactical) (t : FApi.backward) =
  fun tc -> FApi.t_onall t (tt tc)

let (@~+) (tt : FApi.tactical) (ts : FApi.backward list) =
  fun tc -> FApi.t_sub ts (tt tc)

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm

type side    = [`Left|`Right]
type lazyred = EcProofTyping.lazyred

(* -------------------------------------------------------------------- *)
module LowApply = struct
  type ckenv = [
    | `Tc   of rtcenv * ident option
    | `Hyps of EcEnv.LDecl.hyps * proofenv
  ]

  (* ------------------------------------------------------------------ *)
  let hyps_of_ckenv = function
    | `Hyps hyps -> (fst hyps)
    | `Tc (tc, target) -> RApi.tc_hyps ?target tc

  (* ------------------------------------------------------------------ *)
  let sub_hyps (hy1 : LDecl.hyps) (hy2 : LDecl.hyps) =
    if hy1 (*φ*)== hy2 then true else

    let env1, ld1 = LDecl.baseenv hy1, LDecl.tohyps hy1 in
    let env2, ld2 = LDecl.baseenv hy2, LDecl.tohyps hy2 in

    if env1        (*φ*)!= env2        then false else
    if ld1.h_tvar  (*φ*)!= ld2.h_tvar  then false else
    if ld1.h_local (*φ*)== ld2.h_local then true  else

    let env     = env1 in
    let hyps    = LDecl.init env ld1.h_tvar in
    let tophyps = Mid.of_list ld2.h_local in

    let h_eqs (x, v) =
      match Mid.find_opt x tophyps  with
      | None -> false | Some v' ->

        (v (*φ*)== v') ||
          match v, v' with
          | LD_var (t1, f1), LD_var (t2, f2) ->
                EqTest.for_type env t1 t2
             && oeq (is_alpha_eq hyps) f1 f2

          | LD_mem m1, LD_mem m2 ->
             oeq EcMemory.lmt_equal m1 m2

          | LD_modty (mt1, mr1), LD_modty (mt2, mr2) ->
             (mt1 == mt2) && (mr1 == mr2)

          | LD_hyp f1, LD_hyp f2 ->
             is_alpha_eq hyps f1 f2

          | LD_abs_st au1, LD_abs_st au2 ->
             au1 (*φ*)== au2

          | _, _ -> false

   in List.for_all h_eqs ld1.h_local

  (* ------------------------------------------------------------------ *)
  let rec check_pthead (pt : pt_head) (tc : ckenv) =
    let hyps = hyps_of_ckenv tc in

    match pt with
    | PTCut f -> begin
        match tc with
        | `Hyps ( _, _) -> (PTCut f, f)
        | `Tc   (tc, _) ->
            (* cut - create a dedicated subgoal *)
            let handle = RApi.newgoal tc ~hyps f in
            (PTHandle handle, f)
    end

    | PTHandle hd -> begin
        let subgoal =
          match tc with
          | `Hyps tc -> FApi.get_pregoal_by_id hd (snd tc)
          | `Tc   tc -> RApi.tc_get_pregoal_by_id hd (fst tc)
        in
        (* proof reuse - fetch corresponding subgoal*)
        if not (sub_hyps subgoal.g_hyps (hyps_of_ckenv tc)) then
          raise InvalidProofTerm;
        (pt, subgoal.g_concl)
    end

    | PTLocal x -> begin
        let hyps = hyps_of_ckenv tc in
        try  (pt, LDecl.hyp_by_id x hyps)
        with LDecl.LdeclError _ -> raise InvalidProofTerm
    end

    | PTGlobal (p, tys) ->
        (* FIXME: poor API ==> poor error recovery *)
        let env = LDecl.toenv (hyps_of_ckenv tc) in
        (pt, EcEnv.Ax.instanciate p tys env)

  (* ------------------------------------------------------------------ *)
  and check (mode : [`Intro | `Elim]) (pt : proofterm) (tc : ckenv) =
    let hyps = hyps_of_ckenv tc in
    let env  = LDecl.toenv hyps in

    let rec check_args (sbt, ax, nargs) args =
      match args with
      | [] -> (Fsubst.f_subst sbt ax, List.rev nargs)

      | arg :: args ->
          let ((sbt, ax), narg) = check_arg (sbt, ax) arg in
          check_args (sbt, ax, narg :: nargs) args

    and check_arg (sbt, ax) arg =
      let check_binder (x, xty) f =
        let xty = Fsubst.gty_subst sbt xty in

        match xty, arg with
        | GTty xty, PAFormula arg ->
            if not (EcReduction.EqTest.for_type env xty arg.f_ty) then
              raise InvalidProofTerm;
            (Fsubst.f_bind_local sbt x arg, f)

        | GTmem _, PAMemory m ->
            (Fsubst.f_bind_mem sbt x m, f)

        | GTmodty (emt, restr), PAModule (mp, mt) -> begin
          (* FIXME: poor API ==> poor error recovery *)
          try
            EcTyping.check_modtype_with_restrictions env mp mt emt restr;
            EcPV.check_module_in env mp emt;
            (Fsubst.f_bind_mod sbt x mp, f)
          with _ -> raise InvalidProofTerm
        end

        | _ -> raise InvalidProofTerm
      in

      match mode with
      | `Elim -> begin
          match TTC.destruct_product hyps ax, arg with
          | Some (`Imp (f1, f2)), PASub subpt when mode = `Elim ->
              let f1    = Fsubst.f_subst sbt f1 in
              let subpt =
                match subpt with
                | None       -> { pt_head = PTCut f1; pt_args = []; }
                | Some subpt -> subpt
              in
              let subpt, subax = check mode subpt tc in
                if not (EcReduction.is_conv hyps f1 subax) then
                  raise InvalidProofTerm;
                ((sbt, f2), PASub (Some subpt))

          | Some (`Forall (x, xty, f)), _ ->
              (check_binder (x, xty) f, arg)

          | _, _ ->
              if Fsubst.is_subst_id sbt then
                raise InvalidProofTerm;
              check_arg (Fsubst.f_subst_id, Fsubst.f_subst sbt ax) arg
      end

      | `Intro -> begin
          match TTC.destruct_exists hyps ax with
          | Some (`Exists (x, xty, f)) -> (check_binder (x, xty) f, arg)
          | None ->
              if Fsubst.is_subst_id sbt then
                raise InvalidProofTerm;
              check_arg (Fsubst.f_subst_id, Fsubst.f_subst sbt ax) arg
      end
    in

    let (nhd, ax) = check_pthead pt.pt_head tc in
    let ax, nargs = check_args (Fsubst.f_subst_id, ax, []) pt.pt_args in

    ({ pt_head = nhd; pt_args = nargs }, ax)
end

(* -------------------------------------------------------------------- *)
let t_abort (_ : tcenv1) =
  raise InvalidGoalShape

(* -------------------------------------------------------------------- *)
let t_admit (tc : tcenv1) =
  FApi.close (FApi.tcenv_of_tcenv1 tc) VAdmit

(* -------------------------------------------------------------------- *)
let t_fail (tc : tcenv1) =
  tc_error !!tc ~who:"fail" "explicit call to [fail]"

(* -------------------------------------------------------------------- *)
let t_close ?who (t : FApi.backward) (tc : tcenv1) =
  let tc = t tc in

  if not (FApi.tc_done tc) then
    tc_error !$tc ?who "expecting a closed goal";
  tc

(* -------------------------------------------------------------------- *)
let t_id (tc : tcenv1) =
  FApi.tcenv_of_tcenv1 tc

(* -------------------------------------------------------------------- *)
let t_shuffle (ids : EcIdent.t list) (tc : tcenv1) =
  let module E = struct exception InvalidShuffle end in

  try
    let hypstc, concl = FApi.tc1_flat tc in
    let { h_tvar; h_local = hyps } = EcEnv.LDecl.tohyps hypstc in
    let hyps = Mid.of_list hyps in

    let test_fv known fv =
      let test x _ =
        (* Either the variable is in known or was not in the previous hyps,
           in that case the variable is declared in the environment *)
        Mid.mem x known || not (LDecl.has_id x hypstc) in
      if not (Mid.for_all test fv) then raise E.InvalidShuffle in

    let for_form known f = test_fv known f.f_fv in
    let for_type known ty = test_fv known ty.ty_fv in

    let new_ = LDecl.init (LDecl.baseenv hypstc) h_tvar in

    let known, new_ =
      let add1 (known, new_) x =
        if Sid.mem x known then raise E.InvalidShuffle;
        let bd = Mid.find_opt x hyps in
        let bd = oget ~exn:E.InvalidShuffle bd in

        begin match bd with
        | LD_var (ty, f) -> for_type known ty; oiter (for_form known) f

        | LD_hyp f -> for_form known f

        | LD_mem _ | LD_abs_st _ | LD_modty _ -> ()
        end;
        (Sid. add x known, LDecl.add_local x bd new_)

      in List.fold_left add1 (Sid.empty, new_) ids in
    for_form known concl;
    FApi.xmutate1_hyps tc (VShuffle ids) [(new_, concl)]

  with E.InvalidShuffle ->
    tc_error !!tc "invalid shuffle"

(* -------------------------------------------------------------------- *)
let t_change_r ?target action (tc : tcenv1) =
  match target with
  | None -> begin
      let hyps, concl = FApi.tc1_flat tc in
      match action (lazy hyps) concl with
      | None -> tc
      | Some fp when fp == concl -> tc
      | Some fp -> FApi.mutate1 tc (fun hd -> VConv (hd, Sid.empty)) fp
  end

  | Some tg -> begin
      let action hyps fp = action hyps fp |> odfl fp in
      match LDecl.hyp_convert tg action (FApi.tc1_hyps tc) with
      | None      -> tc
      | Some hyps ->
          let concl = FApi.tc1_goal tc in
          FApi.mutate1 tc (fun hd -> VLConv (hd, tg)) ~hyps concl
  end

(* -------------------------------------------------------------------- *)
let t_change ?target (fp : form) (tc : tcenv1) =
  let action (lazy hyps) tgfp =
    if not (EcReduction.is_conv hyps fp tgfp) then
      raise InvalidGoalShape;
    if fp == tgfp then None else Some fp

  in t_change_r ?target action tc

(* -------------------------------------------------------------------- *)
type simplify_t =
  ?target:ident -> ?delta:bool -> ?logic:rlogic_info -> FApi.backward

type simplify_with_info_t =
  ?target:ident -> reduction_info -> FApi.backward

(* -------------------------------------------------------------------- *)
let t_cbv_with_info ?target (ri : reduction_info) (tc : tcenv1) =
  let action (lazy hyps) fp = Some (EcCallbyValue.norm_cbv ri hyps fp) in
  FApi.tcenv_of_tcenv1 (t_change_r ?target action tc)

(* -------------------------------------------------------------------- *)
let t_cbv ?target ?(delta = true) ?(logic = Some `Full) (tc : tcenv1) =
  let ri = if delta then full_red else nodelta in
  let ri = { ri with logic } in
  t_cbv_with_info ?target ri tc

(* -------------------------------------------------------------------- *)
let t_cbn_with_info ?target (ri : reduction_info) (tc : tcenv1) =
  let action (lazy hyps) fp = Some (EcCallbyValue.norm_cbv ri hyps fp) in
  FApi.tcenv_of_tcenv1 (t_change_r ?target action tc)

(* -------------------------------------------------------------------- *)
let t_cbn ?target ?(delta = true) ?(logic = Some `Full) (tc : tcenv1) =
  let ri = if delta then full_red else nodelta in
  let ri = { ri with logic } in
  t_cbv_with_info ?target ri tc

(* -------------------------------------------------------------------- *)
type smode = [ `Cbv | `Cbn ]

let dmode : smode = `Cbv

(* -------------------------------------------------------------------- *)
let t_simplify_with_info ?(mode = dmode) =
  match mode with
  | `Cbn -> t_cbn_with_info
  | `Cbv -> t_cbv_with_info

(* -------------------------------------------------------------------- *)
let t_simplify ?(mode = dmode) =
  match mode with
  | `Cbn -> t_cbn
  | `Cbv -> t_cbv

(* -------------------------------------------------------------------- *)
let t_clears1 ?(leniant = false) xs tc =
  let (hyps, concl) = FApi.tc1_flat tc in

  let xs =
    if not (Mid.set_disjoint xs concl.f_fv) then
      if leniant then Mid.set_diff xs concl.f_fv else
      let ids () = Sid.elements (Mid.set_inter xs concl.f_fv) in
      raise (ClearError (lazy (`ClearInGoal (ids ()))))
    else xs
  in

  if Sid.is_empty xs then tc else

  let hyps =
    try  LDecl.clear ~leniant xs hyps
    with LDecl.LdeclError (LDecl.CannotClear (id1, id2)) ->
      raise (ClearError (lazy (`ClearDep (id1, id2))))
  in

  FApi.mutate1 tc (fun hd -> VConv (hd, xs)) ~hyps concl

(* -------------------------------------------------------------------- *)
let t_clear1 ?leniant x tc =
  t_clears1 ?leniant (Sid.singleton x) tc

(* -------------------------------------------------------------------- *)
let t_clear ?leniant x tc =
  FApi.tcenv_of_tcenv1 (t_clears1 ?leniant (Sid.singleton x) tc)

(* -------------------------------------------------------------------- *)
let t_clears1 ?leniant xs tc =
  t_clears1 ?leniant (Sid.of_list xs) tc

(* -------------------------------------------------------------------- *)
let t_clears ?leniant xs tc =
  FApi.tcenv_of_tcenv1 (t_clears1 ?leniant xs tc)

(* -------------------------------------------------------------------- *)
module LowIntro = struct
  let valid_anon_name chk x =
    if x <> "" then
      x.[0] = '`' && chk (String.sub x 1 (String.length x - 1))
    else false

  let valid_name chk x =
    x = "_" || chk x || valid_anon_name chk x

  let valid_value_name (x : symbol) = valid_name EcIo.is_sym_ident x
  let valid_mod_name   (x : symbol) = valid_name EcIo.is_mod_ident x
  let valid_mem_name   (x : symbol) = valid_name EcIo.is_mem_ident x

  type kind = [`Value | `Module | `Memory]

  let tc_no_product (pe : proofenv) ?loc () =
    tc_error pe ?loc "nothing to introduce"

  let check_name_validity pe kind x : unit =
    let ok =
      match kind with
      | `Value  -> valid_value_name (tg_val x)
      | `Module -> valid_mod_name   (tg_val x)
      | `Memory -> valid_mem_name   (tg_val x)
    in
      if not ok then
        tc_error pe ?loc:(tg_tag x) "invalid name: %s" (tg_val x)
end

(* -------------------------------------------------------------------- *)
let t_intros_x (ids : (ident  option) mloc list) (tc : tcenv1) =
  let add_local hyps id sbt x gty =
    let gty = Fsubst.gty_subst sbt gty in
    let id  = tg_map (function
      | Some id -> id
      | None    -> EcEnv.LDecl.fresh_id hyps (EcIdent.name x)) id
    in

    let name = tg_map EcIdent.name id in

    match gty with
    | GTty ty ->
        LowIntro.check_name_validity !!tc `Value name;
        (id, LD_var (ty, None), Fsubst.f_bind_rename sbt x (tg_val id) ty)
    | GTmem me ->
        LowIntro.check_name_validity !!tc `Memory name;
        (id, LD_mem me, Fsubst.f_bind_mem sbt x (tg_val id))
    | GTmodty (i, r) ->
        LowIntro.check_name_validity !!tc `Module name;
        (id, LD_modty (i, r), Fsubst.f_bind_mod sbt x (EcPath.mident (tg_val id)))
  in

  let add_ld id ld hyps =
    EcLocation.set_oloc
      (tg_tag id)
      (fun () -> LDecl.add_local (tg_val id) ld hyps) ()
  in

  let rec intro1 ((hyps, concl), sbt) id =
    match EcFol.sform_of_form concl with
    | SFquant (Lforall, (x, gty), lazy concl) ->
        let (id, ld, sbt) = add_local hyps id sbt x gty in
        let hyps = add_ld id ld hyps in
        (hyps, concl), sbt

    | SFimp (prem, concl) ->
        let prem = Fsubst.f_subst sbt prem in
        let id   = tg_map (function
          | None    -> EcIdent.create "_"
          | Some id -> id) id in
        let hyps = add_ld id (LD_hyp prem) hyps in
        (hyps, concl), sbt

    | SFlet (LSymbol (x, xty), xe, concl) ->
        let id   = tg_map (function
          | None    -> EcEnv.LDecl.fresh_id hyps (EcIdent.name x)
          | Some id -> id) id in
        let xty  = sbt.fs_ty xty in
        let xe   = Fsubst.f_subst sbt xe in
        let sbt  = Fsubst.f_bind_rename sbt x (tg_val id) xty in
        let hyps = add_ld id (LD_var (xty, Some xe)) hyps in
        (hyps, concl), sbt

    | _ when sbt !=(*φ*) Fsubst.f_subst_id ->
        let concl = Fsubst.f_subst sbt concl in
        intro1 ((hyps, concl), Fsubst.f_subst_id) id

    | _ ->
        match h_red_opt full_red hyps concl with
        | None       -> LowIntro.tc_no_product !!tc ?loc:(tg_tag id) ()
        | Some concl -> intro1 ((hyps, concl), sbt) id
  in

  let tc = FApi.tcenv_of_tcenv1 tc in

  if List.is_empty ids then tc else begin
    let sbt = Fsubst.f_subst_id in
    let (hyps, concl), sbt =
      List.fold_left intro1 (FApi.tc_flat tc, sbt) ids in
    let concl = Fsubst.f_subst sbt concl in
    let (tc, hd) = FApi.newgoal tc ~hyps concl in
    FApi.close tc (VIntros (hd, List.map tg_val ids))
  end

(* -------------------------------------------------------------------- *)
let t_intros (ids : ident mloc list) (tc : tcenv1) =
  t_intros_x (List.map (tg_map some) ids) tc

(* -------------------------------------------------------------------- *)
type iname  = [
  | `Symbol of symbol
  | `Fresh
  | `Ident  of EcIdent.t
]

type inames = [`Symbol of symbol list | `Ident of EcIdent.t list]

(* -------------------------------------------------------------------- *)
let t_intros_n (n : int) (tc : tcenv1) =
  t_intros_x (EcUtils.List.make n (notag None)) tc

(* -------------------------------------------------------------------- *)
let t_intro_i_x (id : EcIdent.t option) (tc : tcenv1) =
  t_intros_x [notag id] tc

(* -------------------------------------------------------------------- *)
let t_intro_i (id : EcIdent.t) (tc : tcenv1) =
  t_intro_i_x (Some id) tc

(* -------------------------------------------------------------------- *)
let t_intro_s (id : iname) (tc : tcenv1) =
  match id with
  | `Symbol x -> t_intro_i_x (Some (EcIdent.create x)) tc
  | `Ident  x -> t_intro_i_x (Some x) tc
  | `Fresh    -> t_intro_i_x None tc

(* -------------------------------------------------------------------- *)
let t_intros_i (ids : EcIdent.t list) (tc : tcenv1) =
  t_intros_x (List.map (notag |- some) ids) tc

(* -------------------------------------------------------------------- *)
let t_intros_s (ids : inames) (tc : tcenv1) =
  match ids with
  | `Symbol x -> t_intros_i (List.map EcIdent.create x) tc
  | `Ident  x -> t_intros_i x tc

(* -------------------------------------------------------------------- *)
let t_intros_i_1 (ids : EcIdent.t list) (tc : tcenv1) =
  FApi.as_tcenv1 (t_intros_i ids tc)

(* -------------------------------------------------------------------- *)
let t_intros_i_seq ?(clear = false) ids tt tc =
  let tt = if clear then FApi.t_seq tt (t_clears ids) else tt in
  FApi.t_focus tt (t_intros_i ids tc)

(* -------------------------------------------------------------------- *)
let t_intros_s_seq ids tt tc =
  FApi.t_focus tt (t_intros_s ids tc)

(* -------------------------------------------------------------------- *)
let tt_apply (pt : proofterm) (tc : tcenv) =
  let (hyps, concl) = FApi.tc_flat tc in
  let tc, (pt, ax)  =
    RApi.to_pure (fun tc -> LowApply.check `Elim pt (`Tc (tc, None))) tc in
  if not (EcReduction.is_conv hyps ax concl) then
    raise InvalidGoalShape;
  FApi.close tc (VApply pt)


(* -------------------------------------------------------------------- *)
let tt_apply_hyp (x : EcIdent.t) ?(args = []) ?(sk = 0) tc =
  let pt =
    let args = (List.map paformula args) @ (List.make sk (PASub None)) in
    { pt_head = PTLocal x; pt_args = args; } in

  tt_apply pt tc

(* -------------------------------------------------------------------- *)
let tt_apply_s (p : path) tys ?(args = []) ?(sk = 0) tc =
  let pt =
    let args = (List.map paformula args) @ (List.make sk (PASub None)) in
    { pt_head = PTGlobal (p, tys); pt_args = args; } in

  tt_apply pt tc

(* -------------------------------------------------------------------- *)
let tt_apply_hd (hd : handle) ?(args = []) ?(sk = 0) tc =
  let pt =
    let args = (List.map paformula args) @ (List.make sk (PASub None)) in
    { pt_head = PTHandle hd; pt_args = args; } in

  tt_apply pt tc

(* -------------------------------------------------------------------- *)
let t_apply (pt : proofterm) (tc : tcenv1) =
  tt_apply pt (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let t_apply_hyp (x : EcIdent.t) ?args ?sk tc =
  tt_apply_hyp x ?args ?sk (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let t_hyp (x : EcIdent.t) tc =
  t_apply_hyp x ~args:[] ~sk:0 tc

(* -------------------------------------------------------------------- *)
let t_apply_s (p : path) (tys : ty list) ?args ?sk tc =
  tt_apply_s p tys ?args ?sk (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
let t_apply_hd (hd : handle) ?args ?sk tc =
  tt_apply_hd hd ?args ?sk (FApi.tcenv_of_tcenv1 tc)

(* -------------------------------------------------------------------- *)
module Apply = struct
  type reason = [`DoNotMatch | `IncompleteInference]

  exception NoInstance of (bool * reason * PT.pt_env * (form * form))

  let t_apply_bwd_r ?(mode = fmdelta) ?(canview = true) pt (tc : tcenv1) =
    let ((hyps, concl), pterr) = (FApi.tc1_flat tc, PT.copy pt.ptev_env) in

    let noinstance ?(dpe = false) reason =
      raise (NoInstance (dpe, reason, pterr, (pt.ptev_ax, concl))) in

    let rec instantiate canview istop pt =
      match istop && PT.can_concretize pt.PT.ptev_env with
      | true ->
          let ax = PT.concretize_form pt.PT.ptev_env pt.PT.ptev_ax in
          if   EcReduction.is_conv hyps ax concl
          then pt
          else instantiate canview false pt

      | false -> begin
          try
            PT.pf_form_match ~mode pt.PT.ptev_env ~ptn:pt.PT.ptev_ax concl;
            if not (PT.can_concretize pt.PT.ptev_env) then
              noinstance `IncompleteInference;
            pt
          with EcMatching.MatchFailure ->
            match TTC.destruct_product hyps pt.PT.ptev_ax with
            | Some _ ->
                (* FIXME: add internal marker *)
                instantiate canview false (PT.apply_pterm_to_hole pt)

            | None when not canview ->
                noinstance `DoNotMatch

            | None ->
                let forview (p, fs) =
                  (* Current proof-term is view argument *)
                  (* Copy PT environment to set a back-track point *)
                  let ptenv = PT.copy pt.ptev_env in
                  let argpt = { pt with ptev_env = ptenv } in
                  let argpt = { ptea_env = argpt.ptev_env;
                                ptea_arg = PVASub argpt; } in

                  (* Type-check view - FIXME: the current API is perfectible *)
                  let viewpt = PT.pt_of_global_r ptenv p [] in
                  let viewpt =
                    List.fold_left
                      (fun viewpt arg -> apply_pterm_to_arg_r viewpt (PVAFormula arg))
                      viewpt fs in

                  (* Apply view to its actual arguments *)
                  let viewpt = apply_pterm_to_arg viewpt argpt in

                  try  Some (instantiate false true viewpt)
                  with NoInstance _ -> None
                in

                let views =
                  match sform_of_form pt.PT.ptev_ax with
                  | SFiff (f1, f2) ->
                      [(LG.p_iff_rl, [f1; f2]);
                       (LG.p_iff_lr, [f1; f2])]

                  | SFnot f1 ->
                      [(LG.p_negbTE, [f1])]

                  | _ -> []
                in

                try  List.find_map forview views
                with Not_found -> noinstance `DoNotMatch
      end
    in

    let pt = instantiate canview true pt in
    let pt = fst (PT.concretize pt) in

    t_apply pt tc

  let t_apply_bwd ?mode ?canview pt (tc : tcenv1) =
    let hyps   = FApi.tc1_hyps tc in
    let pt, ax = LowApply.check `Elim pt (`Hyps (hyps, !!tc)) in
    let ptenv  = ptenv_of_penv hyps !!tc in
    let pt     = { ptev_env = ptenv; ptev_pt = pt; ptev_ax = ax; } in
    t_apply_bwd_r ?mode ?canview pt tc

  let t_apply_bwd_hi ?(dpe = true) ?mode ?canview pt (tc : tcenv1) =
    try  t_apply_bwd ?mode ?canview pt tc
    with (NoInstance (_, r, pt, f)) ->
      tc_error_exn !!tc (NoInstance (dpe, r, pt, f))
end

(* -------------------------------------------------------------------- *)
type genclear = [`Clear | `TryClear | `NoClear]

let t_generalize_hyps_x ?(missing = false) ?naming ?(letin = false) ids tc =
  let env, hyps, concl = FApi.tc1_eflat tc in

  let fresh x =
    match naming with
    | None   -> EcIdent.fresh x
    | Some f ->
      match f x with
      | None   -> EcIdent.fresh x
      | Some x -> EcIdent.create x
  in

  let rec for1 (s, bds, args, cls) (clid, id) =
    try
      let cls =
        match clid with
        | `TryClear -> (true , id) :: cls
        | `Clear    -> (false, id) :: cls
        | `NoClear  -> cls
      in

      match LDecl.ld_subst s (LDecl.by_id id hyps) with
      | LD_var (ty, Some body) when letin ->
          let x    = fresh id in
          let s    = Fsubst.f_bind_rename s id x ty in
          let bds  = `LetIn (x, GTty ty, body) :: bds in
          let args = args in
          (s, bds, args, cls)

      | LD_var (ty, _) ->
          let x    = fresh id in
          let s    = Fsubst.f_bind_rename s id x ty in
          let bds  = `Forall (x, GTty ty) :: bds in
          let args = PAFormula (f_local id ty) :: args in
          (s, bds, args, cls)

      | LD_mem mt ->
        let x    = fresh id in
        let s    = Fsubst.f_bind_mem s id x in
        let bds  = `Forall (x, GTmem mt) :: bds in
        let args = PAMemory id :: args in
        (s, bds, args, cls)

      | LD_modty (mt,r) ->
        let x    = fresh id in
        let s    = Fsubst.f_bind_mod s id (EcPath.mident x) in
        let mp   = EcPath.mident id in
        let sig_ = (EcEnv.Mod.by_mpath mp env).EcModules.me_sig in
        let bds  = `Forall (x, GTmodty (mt, r)) :: bds in
        let args = PAModule (mp, sig_) :: args in
        (s, bds, args, cls)

      | LD_hyp f ->
        let bds  = `Imp f :: bds in
        let args = palocal id :: args in
        (s, bds, args, cls)

      | LD_abs_st _ ->
          raise InvalidGoalShape

    with LDecl.LdeclError _ when missing -> (s, bds, args, cls)

  in

  let (s, bds, args, cls) = (Fsubst.f_subst_id, [], [], []) in
  let (s, bds, args, cls) = List.fold_left for1 (s, bds, args, cls) ids in

  let cltry, cldo = List.partition fst cls in
  let cltry, cldo = (List.map snd cltry, List.map snd cldo) in

  let ff =
    List.fold_left
      (fun ff bd ->
        match bd with
        | `Forall (x, xty)  -> f_forall [x, xty] ff
        | `Imp    pre       -> f_imp pre ff
        | `LetIn  (x, _, f) -> f_let1 x f ff)
      (Fsubst.f_subst s concl) bds in

  let pt = { pt_head = PTCut ff; pt_args = List.rev args; } in
  let tc = t_apply pt tc in
  let ct = fun tc -> tc
    |> t_clears1 ~leniant:true  cltry
    |> t_clears1 ~leniant:false cldo
    |> FApi.tcenv_of_tcenv1

  in FApi.t_onall ct tc

let t_generalize_hyps ?(clear = `No) ?missing ?naming ?letin ids tc =
  let ids =
    match clear with
    | `Yes -> List.map (fun x -> (`Clear   , x)) ids
    | `Try -> List.map (fun x -> (`TryClear, x)) ids
    | `No  -> List.map (fun x -> (`NoClear , x)) ids
  in t_generalize_hyps_x ?missing ?naming ?letin ids tc

let t_generalize_hyp ?clear ?missing ?naming ?letin id tc =
  t_generalize_hyps ?clear ?missing ?naming ?letin [id] tc

(* -------------------------------------------------------------------- *)
module LowAssumption = struct
  (* ------------------------------------------------------------------ *)
  let gen_find_in_hyps test hyps =
    let test (_, lk) =
      match lk with
      | LD_hyp f  -> test f
      | _         -> false
    in
      fst (List.find test (LDecl.tohyps hyps).h_local)

  (* ------------------------------------------------------------------ *)
  let t_gen_assumption tests tc =
    let (hyps, concl) = FApi.tc1_flat tc in

    let hyp =
      try
        List.find_map
          (fun test ->
            try  Some (gen_find_in_hyps (test hyps concl) hyps)
            with Not_found -> None)
          tests
      with Not_found -> tc_error !!tc "no assumption"
    in
    FApi.t_internal (t_hyp hyp) tc
end

(* -------------------------------------------------------------------- *)
let alpha_find_in_hyps hyps f =
   LowAssumption.gen_find_in_hyps (EcReduction.is_alpha_eq hyps f) hyps

let t_assumption mode (tc : tcenv1) =
  let convs =
    match mode with
    | `Alpha -> [EcReduction.is_alpha_eq]
    | `Conv  -> [EcReduction.is_alpha_eq; EcReduction.is_conv]
  in
    LowAssumption.t_gen_assumption convs tc

(* -------------------------------------------------------------------- *)
let t_cut (fp : form) (tc : tcenv1) =
  let concl = FApi.tc1_goal tc in
  t_apply_s LG.p_cut_lemma [] ~args:[fp; concl] ~sk:2 tc

(* -------------------------------------------------------------------- *)
let t_cutdef (pt : proofterm) (fp : form) (tc : tcenv1) =
  FApi.t_first (t_apply pt) (t_cut fp tc)

(* -------------------------------------------------------------------- *)
let t_true (tc : tcenv1) =
  t_apply_s LG.p_true_intro [] tc

(* -------------------------------------------------------------------- *)
let t_reflex_s (f : form) (tc : tcenv1) =
  t_apply_s LG.p_eq_refl [f.f_ty] ~args:[f] tc

let t_reflex ?reduce (tc : tcenv1) =
  let t_reflex_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFeq (f1, _f2) -> t_reflex_s f1 tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_reflex_r tc

(* -------------------------------------------------------------------- *)
let t_symmetry_s f1 f2 tc =
  t_apply_s LG.p_eq_sym_imp [f1.f_ty] ~args:[f2; f1] ~sk:1 tc

let t_symmetry ?reduce (tc : tcenv1) =
  let t_symmetry_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFeq (f1, f2) -> t_symmetry_s f1 f2 tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_symmetry_r tc

(* -------------------------------------------------------------------- *)
let t_transitivity_s f1 f2 f3 tc =
  t_apply_s LG.p_eq_trans [f1.f_ty] ~args:[f1; f2; f3] ~sk:2 tc

let t_transitivity ?reduce f2 (tc : tcenv1) =
  let t_transitivity_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFeq (f1, f3) -> t_transitivity_s f1 f2 f3 tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_transitivity_r tc

(* -------------------------------------------------------------------- *)
let t_exists_intro_s (args : pt_arg list) (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let pt = { pt_head = PTHandle (FApi.tc1_handle tc);
             pt_args = args; } in
  let ax = snd (LowApply.check `Intro pt (`Hyps (hyps, !!tc))) in
  FApi.xmutate1 tc (`Exists args) [ax]

(* -------------------------------------------------------------------- *)
let t_or_intro_s opsym (side : side) (f1, f2 : form pair) (tc : tcenv1) =
  let p =
    match side, opsym with
    | `Left , `Asym -> LG.p_ora_intro_l
    | `Right, `Asym -> LG.p_ora_intro_r
    | `Left , `Sym  -> LG.p_or_intro_l
    | `Right, `Sym  -> LG.p_or_intro_r
  in
  t_apply_s p [] ~args:[f1; f2] ~sk:1 tc

let t_or_intro ?reduce (side : side) (tc : tcenv1) =
  let t_or_intro_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFor (b, (left, right)) -> t_or_intro_s b side (left, right) tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_or_intro_r tc

let t_left  ?reduce tc = t_or_intro ?reduce `Left  tc
let t_right ?reduce tc = t_or_intro ?reduce `Right tc

(* -------------------------------------------------------------------- *)
let t_and_intro_s opsym (f1, f2 : form pair) (tc : tcenv1) =
  let p =
    match opsym with
    | `Asym -> LG.p_anda_intro
    | `Sym  -> LG.p_and_intro
  in

  t_apply_s p [] ~args:[f1; f2] ~sk:2 tc

let t_and_intro ?reduce (tc : tcenv1) =
  let t_and_intro_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFand (b, (left, right)) -> t_and_intro_s b (left, right) tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_and_intro_r tc

(* -------------------------------------------------------------------- *)
let t_iff_intro_s (f1, f2 : form pair) (tc : tcenv1) =
  t_apply_s LG.p_iff_intro [] ~args:[f1; f2] ~sk:2 tc

let t_iff_intro ?reduce (tc : tcenv1) =
  let t_iff_intro_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFiff (f1, f2) -> t_iff_intro_s (f1, f2) tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_iff_intro_r tc

(* -------------------------------------------------------------------- *)
let gen_tuple_intro tys =
  let var ty name i =
    let var = EcIdent.create (Printf.sprintf "%s%d" name (i+1)) in
    (var, f_local var ty) in

  let eq i ty =
    let (x, fx) = var ty "x" i in
    let (y, fy) = var ty "y" i in
    ((x, fx), (y, fy), f_eq fx fy) in

  let eqs   = List.mapi eq tys in
  let concl = f_eq (f_tuple (List.map (snd |- proj3_1) eqs))
                   (f_tuple (List.map (snd |- proj3_2) eqs)) in
  let concl = f_imps (List.map proj3_3 eqs) concl in
  let concl =
    let bindings =
      let for1 ((x, fx), (y, fy), _) bindings =
        (x, GTty fx.f_ty) :: (y, GTty fy.f_ty) :: bindings in
      List.fold_right for1 eqs [] in
    f_forall bindings concl
  in

  concl

(* -------------------------------------------------------------------- *)
let pf_gen_tuple_intro tys hyps pe =
  let fp = gen_tuple_intro tys in
  FApi.newfact pe (VExtern (`TupleCongr tys, [])) hyps fp

(* -------------------------------------------------------------------- *)
let t_tuple_intro_s (fs : form pair list) (tc : tcenv1) =
  let tc  = RApi.rtcenv_of_tcenv1 tc in
  let tys = List.map (fun f -> (fst f).f_ty) fs in
  let hd  = RApi.bwd_of_fwd (pf_gen_tuple_intro tys (RApi.tc_hyps tc)) tc in
  let fs  = List.flatten (List.map (fun (x, y) -> [x; y]) fs) in

  RApi.of_pure_u (tt_apply_hd hd ~args:fs ~sk:(List.length tys)) tc;
  RApi.tcenv_of_rtcenv tc

let t_tuple_intro ?reduce (tc : tcenv1) =
  let t_tuple_intro_r (fp : form) (tc : tcenv1) =
    match sform_of_form fp with
    | SFeq (f1, f2) when is_tuple f1 && is_tuple f2 ->
        let fs = List.combine (destr_tuple f1) (destr_tuple f2) in
        t_tuple_intro_s fs tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_tuple_intro_r tc

(* -------------------------------------------------------------------- *)
let t_elim_r ?(reduce = (`Full : lazyred)) txs tc =
  match sform_of_form (FApi.tc1_goal tc) with
  | SFimp (f1, f2) ->
      let rec aux f1 =
        let sf1 = sform_of_form f1 in

        match
          List.opick (fun tx ->
              try  Some (tx (f1, sf1) f2 tc)
              with TTC.NoMatch -> None)
            txs
        with
        | Some gs -> gs
        | None    -> begin
          let strategy =
            match reduce with
            | `None    -> raise InvalidGoalShape
            | `Full    -> EcReduction.full_red
            | `NoDelta -> EcReduction.nodelta in

            match h_red_opt strategy (FApi.tc1_hyps tc) f1 with
            | None    -> raise InvalidGoalShape
            | Some f1 -> aux f1
        end
      in
        aux f1

    | _ -> raise InvalidGoalShape

(* -------------------------------------------------------------------- *)
let t_elim_false_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFfalse -> t_apply_s LG.p_false_elim [] ~args:[concl] tc
  | _ -> raise TTC.NoMatch

let t_elim_false ?reduce tc = t_elim_r ?reduce [t_elim_false_r] tc

(* --------------------------------------------------------------------- *)
let t_elim_and_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFand (opsym, (a1, a2)) ->
      let p =
        match opsym with
        | `Asym -> LG.p_anda_elim
        | `Sym  -> LG.p_and_elim

      in t_apply_s p [] ~args:[a1; a2; concl] ~sk:1 tc

  | _ -> raise TTC.NoMatch

let t_elim_and ?reduce goal = t_elim_r ?reduce [t_elim_and_r] goal

(* --------------------------------------------------------------------- *)
let t_elim_or_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFor (opsym, (a1, a2)) ->
      let p =
        match opsym with
        | `Asym -> LG.p_ora_elim
        | `Sym  -> LG.p_or_elim

      in t_apply_s p [] ~args:[a1; a2; concl] ~sk:2 tc

  | _ -> raise TTC.NoMatch

let t_elim_or ?reduce tc = t_elim_r ?reduce [t_elim_or_r] tc

(* --------------------------------------------------------------------- *)
let t_elim_iff_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFiff (a1, a2) ->
      t_apply_s LG.p_iff_elim [] ~args:[a1; a2; concl] ~sk:1 tc
  | _ -> raise TTC.NoMatch

let t_elim_iff ?reduce tc = t_elim_r ?reduce [t_elim_iff_r] tc

(* -------------------------------------------------------------------- *)
let t_elim_if_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFif (a1, a2, a3) ->
      t_apply_s LG.p_if_elim [] ~args:[a1; a2; a3; concl] ~sk:2 tc
  | _ -> raise TTC.NoMatch

let t_elim_if ?reduce tc = t_elim_r ?reduce [t_elim_if_r] tc

(* -------------------------------------------------------------------- *)
let gen_tuple_eq_elim (tys : ty list) : form =
  let p  = EcIdent.create "p" in
  let fp = f_local p tbool in

  let var ty name i =
    let var = EcIdent.create (Printf.sprintf "%s%d" name (i+1)) in
    (var, f_local var ty) in

  let eq i ty =
    let (x, fx) = var ty "x" i in
    let (y, fy) = var ty "y" i in
    ((x, fx), (y, fy), f_eq fx fy) in

  let eqs   = List.mapi eq tys in
  let concl = f_eq (f_tuple (List.map (snd |- proj3_1) eqs))
                   (f_tuple (List.map (snd |- proj3_2) eqs)) in
  let concl = f_imps [f_imps (List.map proj3_3 eqs) fp; concl] fp in
  let concl =
    let bindings =
      let for1 ((x, fx), (y, fy), _) bindings =
        (x, GTty fx.f_ty) :: (y, GTty fy.f_ty) :: bindings in
      List.fold_right for1 eqs [] in
    f_forall bindings concl
  in

  f_forall [(p, GTty tbool)] concl

(* -------------------------------------------------------------------- *)
let pf_gen_tuple_eq_elim tys hyps pe =
  let fp = gen_tuple_eq_elim tys in
  FApi.newfact pe (VExtern (`TupleEqElim tys, [])) hyps fp

(* -------------------------------------------------------------------- *)

let t_elim_eq_tuple_r_n ((_, sf) : form * sform) concl tc =
  match sf with
  | SFeq (a1, a2) when is_tuple a1 && is_tuple a2 ->
      let tc   = RApi.rtcenv_of_tcenv1 tc in
      let hyps = RApi.tc_hyps tc in
      let fs   = List.combine (destr_tuple a1) (destr_tuple a2) in
      let tys  = List.map (f_ty |- fst) fs in
      let hd   = RApi.bwd_of_fwd (pf_gen_tuple_eq_elim tys hyps) tc in
      let args = List.flatten (List.map (fun (x, y) -> [x; y]) fs) in
      let args = concl :: args in

      RApi.of_pure_u (tt_apply_hd hd ~args ~sk:1) tc;
      List.length tys, RApi.tcenv_of_rtcenv tc

  | _ -> raise TTC.NoMatch

let t_elim_eq_tuple_r f concl tc = snd (t_elim_eq_tuple_r_n f concl tc)

let t_elim_eq_tuple ?reduce goal = t_elim_r ?reduce [t_elim_eq_tuple_r] goal

(* -------------------------------------------------------------------- *)
let t_elim_exists_r ((f, _) : form * sform) concl tc =
  match f.f_node with
  | Fquant (Lexists, bd, body) ->
      let subst = Fsubst.f_subst_init ~freshen:true () in
      let subst, bd = Fsubst.add_bindings subst bd in
      let newc  = f_forall bd (f_imp (Fsubst.f_subst subst body) concl) in
      let tc    = FApi.mutate1 tc (fun hd -> VExtern (`Exists, [hd])) newc in
      FApi.tcenv_of_tcenv1 tc
  | _ -> raise TTC.NoMatch

let t_elim_exists ?reduce tc = t_elim_r ?reduce [t_elim_exists_r] tc

(* -------------------------------------------------------------------- *)
(* FIXME: document this function ! *)
let t_elimT_form (ind : proofterm) ?(sk = 0) (f : form) (tc : tcenv1) =
  let tc    = FApi.tcenv_of_tcenv1 tc in
  let _, ax =
    snd (RApi.to_pure (fun tc -> LowApply.check `Elim ind (`Tc (tc, None))) tc) in

  let hyps, concl = FApi.tc_flat tc in
  let env = LDecl.toenv hyps in

  let rec skip i a f =
    match i, EcFol.sform_of_form f with
    | Some i, _ when i <= 0 -> (a, f)
    | Some i, SFimp (_, f2) -> skip (Some (i-1)) (a+1) f2
    | None  , SFimp (_, f2) -> skip None (a+1) f2
    | Some _, _ -> raise InvalidGoalShape
    | None  , _ -> (a, f)
  in

  let (pr, prty, ax) =
    match sform_of_form ax with
    | SFquant (Lforall, (pr, GTty prty), lazy ax) -> (pr, prty, ax)
    | _ -> raise InvalidGoalShape
  in

  if not (EqTest.for_type env prty (tfun f.f_ty tbool)) then
    raise InvalidGoalShape;

  let (aa1, ax) = skip None 0 ax in

  let (x, _xty, ax) =
    match sform_of_form ax with
    | SFquant (Lforall, (x, GTty xty), lazy ax) -> (x, xty, ax)
    | _ -> raise InvalidGoalShape
  in

  let (aa2, ax) =
    let rec doit ax aa =
      match TTC.destruct_product hyps ax with
      | Some (`Imp (f1, f2)) when Mid.mem pr f1.f_fv -> doit f2 (aa+1)
      | _ -> (aa, ax)
    in
      doit ax 0
  in

  let pf =
    let (_, concl) = skip (Some sk) 0 concl in
    let (z, concl) = EcProofTerm.pattern_form ~name:(EcIdent.name x) hyps ~ptn:f concl in
      Fsubst.f_subst_local pr (f_lambda [(z, GTty f.f_ty)] concl) ax
  in

  let pf_inst = Fsubst.f_subst_local x f pf in

  let (aa3, sk) =
    let rec doit pf_inst (aa, sk) =
      if   EcReduction.is_conv hyps pf_inst concl
      then (aa, sk)
      else
        match TTC.destruct_product hyps pf_inst with
        | Some (`Imp (_, f2)) -> doit f2 (aa+1, sk+1)
        | _ -> raise InvalidGoalShape
    in
      doit pf_inst (0, sk)
  in

  let pf   = f_lambda [(x, GTty f.f_ty)] (snd (skip (Some sk) 0 pf)) in
  let args =
    (PAFormula pf :: (List.make aa1 (PASub None)) @
     PAFormula  f :: (List.make (aa2+aa3) (PASub None))) in
  let pt   = { ind with pt_args = ind.pt_args @ args; } in

  (* FIXME: put first goal last *)
  FApi.t_focus (t_apply pt) tc

(* -------------------------------------------------------------------- *)
let t_elimT_form_global p ?(typ = []) ?sk f tc =
  let pt = { pt_head = PTGlobal (p, typ); pt_args = []; } in
  t_elimT_form pt f ?sk tc

(* -------------------------------------------------------------------- *)
let gen_tuple_elim ?(witheq = true) (tys : ty list) : form =
  let var i ty =
    let var = EcIdent.create (Printf.sprintf "%s%d" "x" (i+1)) in
    (var, f_local var ty) in

  let tty  = ttuple tys in
  let p    = EcIdent.create "p" in
  let fp   = f_local p (tfun tty tbool) in
  let t    = EcIdent.create "t" in
  let ft   = f_local t tty in
  let vars = List.mapi var tys in
  let tf   = f_tuple (List.map snd vars) in

  let indh = f_app fp [tf] tbool in
  let indh = if witheq then f_imp (f_eq ft tf) indh else indh in
  let indh = f_forall (List.map (snd_map (fun f -> GTty f.f_ty)) vars) indh in

  let concl = f_forall [] (f_imp indh (f_app fp [ft] tbool)) in
  let concl = f_forall [t, GTty tty] concl in
  let concl = f_forall [p, GTty (tfun tty tbool)] concl in

  concl

(* -------------------------------------------------------------------- *)
let pf_gen_tuple_elim ?witheq tys hyps pe =
  let fp = gen_tuple_elim ?witheq tys in
  FApi.newfact pe (VExtern (`TupleElim tys, [])) hyps fp

(* -------------------------------------------------------------------- *)
let t_elimT_ind ?reduce mode (tc : tcenv1) =
  let elim (id, ty) tc =
    let tc, pt, sk =
      let env, hyps, _ = FApi.tc1_eflat tc in

      match EcEnv.Ty.scheme_of_ty mode ty env with
      | Some (p, typ) ->
          let pt = { pt_head = PTGlobal (p, typ); pt_args = []; } in
          (tc, pt, 0)

      | None ->
          match (EcEnv.ty_hnorm ty env).ty_node with
          | Ttuple tys ->
              let indtc  = pf_gen_tuple_elim ~witheq:false tys hyps in
              let tc, hd = FApi.bwd1_of_fwd indtc tc in
              let pt     = { pt_head = PTHandle hd; pt_args = []; } in
              (tc, pt, 0)

          | _ when EcReduction.EqTest.for_type env tunit ty ->
              let pt = { pt_head = PTGlobal (LG.p_unit_elim, []);
                         pt_args = []; } in
              (tc, pt, 0)

          | _ when EcReduction.EqTest.for_type env tint ty ->
              let pt = { pt_head = PTGlobal (EcCoreLib.CI_Int.p_int_elim, []);
                         pt_args = []; } in
              (tc, pt, 1)

          | _ when EcReduction.EqTest.for_type env tbool ty ->
              let pt = { pt_head = PTGlobal (LG.p_bool_elim, []);
                         pt_args = []; } in
              (tc, pt, 0)

          | _ -> raise InvalidGoalShape
    in
      t_elimT_form ~sk pt (f_local id ty) tc
  in

  let doit fp tc =
    match sform_of_form fp with
    | SFquant (Lforall, (x, GTty ty), _) -> begin
        let hyps = FApi.tc1_hyps tc in
        let id   = LDecl.fresh_id hyps (EcIdent.name x) in

        FApi.t_seqs
          [t_intros_i_seq ~clear:true [id] (elim (id, ty));
           t_simplify_with_info EcReduction.beta_red]
          tc
      end

    | _ -> raise TTC.NoMatch

  in TTC.t_lazy_match ?reduce doit tc

(* -------------------------------------------------------------------- *)
let t_elim_default_r = [
  t_elim_false_r;
  t_elim_and_r;
  t_elim_or_r;
  t_elim_iff_r;
  t_elim_if_r;
  t_elim_eq_tuple_r;
  t_elim_exists_r;
]

let t_elim ?reduce tc = t_elim_r ?reduce t_elim_default_r tc

(* -------------------------------------------------------------------- *)
let t_case fp tc = t_elimT_form_global LG.p_case_eq_bool fp tc

(* -------------------------------------------------------------------- *)
let t_elim_hyp h tc =
  (* FIXME: exception? *)
  let f  = LDecl.hyp_by_id h (FApi.tc1_hyps tc) in
  let pt = { pt_head = PTLocal h; pt_args = []; } in
  FApi.t_seq (t_cutdef pt f) t_elim tc

(* -------------------------------------------------------------------- *)
let t_elim_prind_r ?reduce ?accept (_mode : [`Case | `Ind]) tc =
  let doit fp tc =
    let env = FApi.tc1_env tc in

    match sform_of_form fp with
    | SFimp (f1, f2) ->
       let (p, sk), tv, args =
         match fst_map f_node (destr_app f1) with
         | Fop (p, tv), args when EcEnv.Op.is_prind env p -> begin
            if is_some accept then
              let pri = oget (EcEnv.Op.by_path_opt p env) in
              let pri = EcDecl.operator_as_prind pri in
              if not (oget accept pri) then
                raise InvalidGoalShape;
           end;
           (oget (EcEnv.Op.scheme_of_prind env `Case p), tv, args)

         | _ -> raise InvalidGoalShape

       in t_apply_s p tv ~args:(args @ [f2]) ~sk tc

    | _ -> raise TTC.NoMatch

  in TTC.t_lazy_match ?reduce doit tc

(* -------------------------------------------------------------------- *)
let t_elim_prind = t_elim_prind_r ?accept:None

(* -------------------------------------------------------------------- *)
let t_elim_iso_and ?reduce tc =
  try
    (2, t_elim_and ?reduce tc)
  with InvalidGoalShape ->
    let outgoals = ref None in

    let accept pri =
      match EcInductive.prind_is_iso_ands pri with
      | None -> false
      | Some (_, ngoals) -> outgoals := Some ngoals; true in

    let tc = t_elim_prind_r ?reduce ~accept `Case tc in (oget !outgoals, tc)

(* -------------------------------------------------------------------- *)
let t_elim_iso_or ?reduce tc =
  try
    ([1; 1], t_elim_or ?reduce tc)
  with InvalidGoalShape ->
    let outgoals = ref None in

    let accept pri =
      match EcInductive.prind_is_iso_ors pri with
      | None -> false
      | Some ((_, n1), (_, n2)) -> outgoals := Some [n1; n2]; true in

    let tc = t_elim_prind_r ?reduce ~accept `Case tc in (oget !outgoals, tc)

(* -------------------------------------------------------------------- *)
let t_split ?(closeonly = false) ?reduce (tc : tcenv1) =
  let t_split_r (fp : form) (tc : tcenv1) =
    let hyps, concl = FApi.tc1_flat tc in

    match sform_of_form fp with
    | SFtrue ->
        t_true tc
    | SFand (b, (f1, f2)) when not closeonly ->
        t_and_intro_s b (f1, f2) tc
    | SFiff (f1, f2) when not closeonly ->
        t_iff_intro_s (f1, f2) tc
    | SFeq (f1, f2) when EcReduction.is_conv hyps f1 f2 ->
        t_reflex_s f1 tc
    | SFeq (f1, f2) when not closeonly && (is_tuple f1 && is_tuple f2) ->
        let fs = List.combine (destr_tuple f1) (destr_tuple f2) in
        t_tuple_intro_s fs tc
    | SFif (cond, _, _) when not closeonly ->
        (* FIXME: simplify goal *)
        let tc = if f_equal concl fp then tc else t_change fp tc in
        let tc = t_case cond tc in
          tc
    | _ -> raise TTC.NoMatch
  in
    TTC.t_lazy_match ?reduce t_split_r tc

(* -------------------------------------------------------------------- *)
let t_split_prind ?reduce (tc : tcenv1) =
  let t_split_r (fp : form) (tc : tcenv1) =
    let env = FApi.tc1_env tc in

    let p, tv, args =
      match fst_map f_node (destr_app fp) with
      | Fop (p, tv), args when EcEnv.Op.is_prind env p ->
         (p, tv, args)
      | _ -> raise InvalidGoalShape in
    let pri = oget (EcEnv.Op.by_path_opt p env) in
    let pri = EcDecl.operator_as_prind pri in

    match EcInductive.prind_is_iso_ands pri with
    | None -> raise InvalidGoalShape
    | Some (x, sk) ->
       let p = EcInductive.prind_introsc_path p x in
       t_apply_s p tv ~args ~sk tc

  in TTC.t_lazy_match ?reduce t_split_r tc

(* -------------------------------------------------------------------- *)
let t_or_intro_prind ?reduce (side : side) (tc : tcenv1) =
  let t_split_r (fp : form) (tc : tcenv1) =
    let env = FApi.tc1_env tc in

    let p, tv, args =
      match fst_map f_node (destr_app fp) with
      | Fop (p, tv), args when EcEnv.Op.is_prind env p ->
         (p, tv, args)
      | _ -> raise InvalidGoalShape in
    let pri = oget (EcEnv.Op.by_path_opt p env) in
    let pri = EcDecl.operator_as_prind pri in

    match EcInductive.prind_is_iso_ors pri with
    | Some ((x, sk), _) when side = `Left ->
       let p = EcInductive.prind_introsc_path p x in
       t_apply_s p tv ~args ~sk tc
    | Some (_, (x, sk)) when side = `Right ->
       let p = EcInductive.prind_introsc_path p x in
       t_apply_s p tv ~args ~sk tc
    | _  -> raise InvalidGoalShape

  in TTC.t_lazy_match ?reduce t_split_r tc

(* -------------------------------------------------------------------- *)
type rwspec = [`LtoR|`RtoL] * ptnpos option
type rwmode = [`Bool | `Eq]

(* -------------------------------------------------------------------- *)
let t_rewrite
   ?xconv ?keyed ?target ?(mode : rwmode option) ?(donot=false)
   (pt : proofterm) (s, pos) (tc : tcenv1)
=
  let tc           = RApi.rtcenv_of_tcenv1 tc in
  let (hyps, tgfp) = RApi.tc_flat ?target tc in
  let env          = LDecl.toenv hyps in
  let (pt, ax)     = LowApply.check `Elim pt (`Tc (tc, target)) in

  let (pt, left, right) =
    let doit ax =
      match sform_of_form ax, mode with
      | SFeq  (f1, f2), (None | Some `Eq) -> (pt, f1, f2)
      | SFiff (f1, f2), (None | Some `Eq) -> (pt, f1, f2)

      | SFnot f, (None | Some `Bool) when s = `LtoR && donot ->
        let ptev_env = ptenv_of_penv hyps (RApi.tc_penv tc) in
        let pt = { ptev_env; ptev_pt = pt; ptev_ax = ax } in
        let pt' = pt_of_global_r ptev_env LG.p_negeqF [] in
        let pt' = apply_pterm_to_arg_r pt' (PVAFormula f) in
        let pt' = apply_pterm_to_arg_r pt' (PVASub pt) in
        let pt, _ = concretize pt' in
        pt, f, f_false

      | _, (None | Some `Bool) when
          s = `LtoR && ER.EqTest.for_type env ax.f_ty tbool
          -> (pt, ax, f_true)

      | _ -> raise TTC.NoMatch
    in oget ~exn:InvalidProofTerm (TTC.lazy_destruct hyps doit ax)
  in

  let (left, right) =
    match s with
    | `LtoR -> (left , right)
    | `RtoL -> (right, left )
  in

  let change f =
    if not (EcReduction.is_conv hyps f left) then
      raise InvalidGoalShape;
    right in

  let npos  =
    match pos with
    | None     -> FPosition.select_form ?keyed ?xconv hyps None left tgfp
    | Some pos -> pos in

  let tgfp =
    try  FPosition.map npos change tgfp
    with InvalidPosition -> raise InvalidGoalShape
  in

  match target with
  | None ->
      let hd   = RApi.newgoal tc tgfp in
      let rwpt = { rpt_proof = pt; rpt_occrs = pos; rpt_lc = None; } in

      RApi.close tc (VRewrite (hd, rwpt));
      RApi.tcenv_of_rtcenv tc

  | Some (h : ident) ->
      let hyps = oget (LDecl.hyp_convert h (fun _ _ -> tgfp) (RApi.tc_hyps tc)) in
      let hd   = RApi.newgoal tc ~hyps (RApi.tc_goal tc) in
      let rwpt = { rpt_proof = pt; rpt_occrs = pos; rpt_lc = Some h; } in

      RApi.close tc (VRewrite (hd, rwpt));
      RApi.tcenv_of_rtcenv tc

(* -------------------------------------------------------------------- *)
let t_rewrite_hyp ?xconv ?mode ?donot (id : EcIdent.t) pos (tc : tcenv1) =
  let pt = { pt_head = PTLocal id; pt_args = []; } in
  t_rewrite ?xconv ?mode ?donot pt pos tc

(* -------------------------------------------------------------------- *)
type vsubst = [
  | `Local of EcIdent.t
  | `Glob  of EcPath.mpath * EcMemory.memory
  | `PVar  of EcTypes.prog_var * EcMemory.memory
]

(* -------------------------------------------------------------------- *)
type subst_kind = {
  sk_local : bool;
  sk_pvar  : bool;
  sk_glob  : bool;
}

let  full_subst_kind = { sk_local = true ; sk_pvar  = true ; sk_glob  = true ; }
let empty_subst_kind = { sk_local = false; sk_pvar  = false; sk_glob  = false; }

type tside = [`All of [`LtoR | `RtoL] option | `LtoR | `RtoL]

(* -------------------------------------------------------------------- *)
module LowSubst = struct
  (* ------------------------------------------------------------------ *)
  let default_subst_kind = full_subst_kind

  (* ------------------------------------------------------------------ *)
  let is_member_for_subst ?kind env var f =
    let kind = odfl default_subst_kind kind in

    match f.f_node, var with
    (* Substitution of logical variables *)
    | Flocal x, None when kind.sk_local ->
        Some (`Local x)

    | Flocal x, Some (`Local y) when kind.sk_local && id_equal x y ->
        Some (`Local x)

    (* Substitution of program variables *)
    | Fpvar (pv, m), None when kind.sk_pvar -> Some (`PVar (pv, m))
    | Fpvar (pv, m), Some (`PVar (pv', m')) when kind.sk_pvar ->
        let pv  = EcEnv.NormMp.norm_pvar env pv  in
        let pv' = EcEnv.NormMp.norm_pvar env pv' in

        if   EcTypes.pv_equal pv pv' && EcMemory.mem_equal m m'
        then Some (`PVar (pv, m))
        else None

    (* Substitution of globs *)
    | Fglob (mp, m), None when kind.sk_glob -> Some (`Glob (mp, m))
    | Fglob (mp, m), Some (`Glob (mp', m')) when kind.sk_glob ->
        let gl  = EcEnv.NormMp.norm_glob env m  mp  in
        let gl' = EcEnv.NormMp.norm_glob env m' mp' in

        if   EcFol.f_equal gl gl'
        then Some (`Glob (mp, m))
        else None

    | _, _ -> None

  (* ------------------------------------------------------------------ *)
  let is_eq_for_subst ?kind ?(tside = (`All None : tside)) hyps var (f1, f2) =
    let can (side : [`LtoR | `RtoL]) =
      match tside with
      | `All  None    -> Some `High
      | `All (Some x) -> Some (if x = side then `High else `Low)
      | _ -> if tside = (side :> tside) then Some `High else None
    in

    let is_member_for_subst ?kind side env var f tg =
      can side |> obind (fun prio ->
        is_member_for_subst ?kind env var f
          |> obind (fun eq -> Some (prio, (side, eq, tg))))
    in

    let env = LDecl.toenv hyps in

    let var = List.pmap identity
      [is_member_for_subst ?kind `LtoR env var f1 f2;
       is_member_for_subst ?kind `RtoL env var f2 f1] in

    let cmp x y =
      let x = match x with `High -> 1 | `Low -> 0 in
      let y = match y with `High -> 1 | `Low -> 0 in
      Pervasives.compare x y in

    let var = List.ksort ~stable:true ~rev:true ~key:fst ~cmp var in
    let var = List.ohead var |> omap snd in

    match var with
    | None -> None

    (* Substitution of logical variables *)
    | Some ((_, `Local x, f) as aout) ->
      let f = simplify { no_red with delta_h = predT } hyps f in
      if Mid.mem x f.f_fv then None else Some aout

    (* Substitution of program variables *)
    | Some ((_, `PVar (pv, m), f) as aout) ->
        let f  = simplify { no_red with delta_h = predT } hyps f in
        let fv = EcPV.PV.fv env m f in
        if EcPV.PV.mem_pv env pv fv then None else Some aout

    (* Substitution of globs *)
    | Some ((_, `Glob (mp, m), f) as aout) ->
        let f  = simplify { no_red with delta_h = predT } hyps f in
        let fv = EcPV.PV.fv env m f in
        if EcPV.PV.mem_glob env mp fv then None else Some aout

  (* ------------------------------------------------------------------ *)
  let build_subst env var f fy =
    match var with
    | `Local x ->
        let subst f = Fsubst.f_subst_local x f in
        let check tg = Mid.mem x tg.f_fv in
        (subst f, omap subst fy, check)

    | `PVar (pv, m) ->
        let subst f = EcPV.PVM.subst env (EcPV.PVM.add env pv m f EcPV.PVM.empty) in
        let check _tg = true in
        (subst f, omap subst fy, check)

    | `Glob (mp, m) ->
        let subst f = EcPV.PVM.subst env (EcPV.PVM.add_glob env mp m f EcPV.PVM.empty) in
        let check _tg = true in
        (subst f, omap subst fy, check)
end

(* -------------------------------------------------------------------- *)
type subst_clear =
  | SCnone (* clear nothing *)
  | SChyp  (* clear the hypothesis *)
  | SCall  (* clear the variable and the hypothesis *)

let t_subst_x ?kind ?tg ?(clear = SCall) ?(gen=false) ?var ?tside ?eqid (tc : tcenv1) =
  let env, hyps, concl = FApi.tc1_eflat tc in

  let subst1 (subst, check) moved (id, lk) =
    if   tg |> omap (fun tg -> not (Sid.mem id tg)) |> odfl false
    then `Pre (id, lk)
    else

    let check tg =
      check tg || not (Mid.disjoint (fun _ _ _ -> false) tg.f_fv moved) in

    match lk with
    | LD_var (_ty, None) ->
        `Pre (id, lk)

    | LD_var (ty, Some body) ->
        if   check body
        then `Post (id, LD_var (ty, Some (subst body)))
        else `Pre  (id, LD_var (ty, Some body))

    | LD_hyp hform ->
        if   check hform
        then `Post (id, LD_hyp (subst hform))
        else `Pre  (id, LD_hyp hform)

    | LD_mem    _ -> `Pre (id, lk)
    | LD_modty  _ -> `Pre (id, lk)
    | LD_abs_st _ -> `Pre (id, lk)
  in

  let substy1 substy (id, lk) =
    match lk with
    | LD_var (ty, Some body) -> id, LD_var(ty, Some (substy body))
    | LD_hyp f -> id, LD_hyp (substy f)
    | _        -> id, lk in

  let eqs =
    eqid
      |> omap  (fun id -> [id, LD_hyp (LDecl.hyp_by_id id hyps)])
      |> ofdfl (fun () -> (LDecl.tohyps hyps).h_local)
  in

  let try1 eq =
    match eq with
    | id, (LD_hyp f as hid)  when is_eq_or_iff f -> begin
        let dosubst (side, var, f) =
          let y, fy =
            if gen then
              let y = EcIdent.create "y" in
              Some y, Some (f_local y f.f_ty)
            else None, None in
          let subst, substy, check = LowSubst.build_subst env var f fy in

          let post, (id', _), pre =
            try  List.find_pivot (id_equal id |- fst) (LDecl.tohyps hyps).h_local
            with Not_found -> assert false
          in

          assert (id_equal id id');

          let pre, hpost, hposty, _ =
            List.fold_right
              (fun h (pre, hpost, hposty, moved) ->
                assert (not (id_equal (fst h) id));
                match h, var with
                | (x, _), _ ->
                  match subst1 (subst, check) moved h with
                  | `Pre  (id, lk) -> ((id, lk) :: pre, hpost, hposty, moved)
                  | `Post (id, lk) ->
                      match lk with
                      | LD_var (_, _) -> (pre, (id, lk) :: hpost, h::hposty, Sid.add x moved)
                      | _             -> (pre, (id, lk) :: hpost, h::hposty, moved))
              pre ([], [], [], Sid.empty) in

          let posty = post in
          let post =
            List.fold_right
              (fun h post ->
                assert (not (id_equal (fst h) id));
                match subst1 (subst, check) Sid.empty h with
                | `Pre (id, lk) | `Post (id, lk) -> (id, lk) :: post )
              post [] in

          let concl' = subst concl in
          let hyps'  = hpost @ post @ (if clear = SCnone then (id, hid)::pre else pre) in
          let hyps'  =
            LDecl.init (LDecl.baseenv hyps)
              ~locals:hyps' (LDecl.tohyps hyps).h_tvar in

          let togen =
            match y with
            | None -> None
            | Some y ->
              let substy = oget substy in
              let all = hposty @ posty in
              Some (y, substy1 substy, all, side, var, f) in

          let clear  =
            match var with
            | `Local x when clear <> SCnone -> begin
              match LDecl.by_id x hyps with
              | LD_var (_, None) -> t_clear x
              | _ -> t_id
            end
            | _ -> t_id
          in

          FApi.t_focus clear (FApi.xmutate1_hyps tc `Subst [hyps', concl']), togen
        in

        try
          LowSubst.is_eq_for_subst
            ?kind ?tside hyps var (destr_eq_or_iff f)
          |> omap dosubst
        with EcPV.MemoryClash -> None
    end

    | _ -> None
  in

  try  List.find_map try1 eqs
  with Not_found -> raise InvalidGoalShape

let t_subst ?kind ?tg ?(clear = true) ?var ?tside ?eqid (tc : tcenv1) =
  let clear = if clear then SCall else SChyp in
  fst (t_subst_x ?kind ?tg ~clear ~gen:false ?var ?tside ?eqid tc)

(* -------------------------------------------------------------------- *)
let t_absurd_hyp ?(conv  = `AlphaEq) id tc =
  let hyps, concl = FApi.tc1_flat tc in

  let b, f = destr_nots (LDecl.hyp_by_id id hyps) in

  let test f' =
    let b', f' = destr_nots f' in
    (b = not b') && EcReduction.xconv conv hyps f f' in

  let id' =
    try  LowAssumption.gen_find_in_hyps test hyps
    with _ -> raise InvalidGoalShape
  in

  let x, hnx, hx = if b then f, id, id' else f_not f, id', id in

  FApi.t_internal (FApi.t_seqs [
    t_apply_s LG.p_false_elim [] ~args:[concl] ~sk:1;
    FApi.t_seqsub (t_apply_s LG.p_negbTE [] ~args:[x] ~sk:2)
      [ t_apply_hyp hnx; t_apply_hyp hx ]
  ]) tc

(* -------------------------------------------------------------------- *)
let t_absurd_hyp ?conv ?id tc =
  let tabsurd = t_absurd_hyp ?conv in

  match id with
  | Some id -> tabsurd id tc
  | None    ->
      let tott (id, lk) =
        match lk with
        | LD_hyp f when is_not f -> Some (tabsurd id)
        | _ -> None

      in let hyps = (LDecl.tohyps (FApi.tc1_hyps tc)).h_local
      in let tc = FApi.t_try (FApi.t_ors_pmap tott hyps) tc in

      if not (FApi.tc_done tc) then raise InvalidGoalShape; tc

(* -------------------------------------------------------------------- *)
let t_false ?(conv = `Eq) id tc =
  let hy = FApi.tc1_hyps tc in
  let hh = LDecl.hyp_by_id id hy in

  if not (EcReduction.xconv conv hy hh f_false) then
    raise InvalidGoalShape;

  FApi.t_internal ~info:"t_false"
    (FApi.t_seq
       (t_generalize_hyp ~clear:`No id) t_elim_false)
    tc

(* -------------------------------------------------------------------- *)
let t_false ?conv ?id tc =
  let tfalse = t_false ?conv in

  match id with
  | Some id -> tfalse id tc
  | None    ->
      let tott (id, lk) =
        match lk with
        | LD_hyp _ -> Some (tfalse id)
        | _ -> None

      in let hyps = (LDecl.tohyps (FApi.tc1_hyps tc)).h_local
      in FApi.t_ors_pmap tott hyps tc

(* -------------------------------------------------------------------- *)
type pgoptions =  {
  pgo_split  : bool;
  pgo_solve  : bool;
  pgo_subst  : bool;
  pgo_disjct : bool;
  pgo_delta  : pgo_delta;
}

and pgo_delta = {
  pgod_case  : bool;
  pgod_split : bool;
}

module PGOptions = struct
  let default =
    let fordelta =
      { pgod_case  = false;
        pgod_split = true ; }; in

    { pgo_split  = true;
      pgo_solve  = true;
      pgo_subst  = true;
      pgo_disjct = false;
      pgo_delta  = fordelta; }

  let merged1 opts (b, x) =
    match x with
    | None -> { pgod_case = b; pgod_split = b; }
    | Some `Case  -> { opts with pgod_case  = b; }
    | Some `Split -> { opts with pgod_split = b; }

  let merge1 opts ((b, x) : bool * EcParsetree.ppgoption) =
    match x with
    | `Split       -> { opts with pgo_split  = b; }
    | `Solve       -> { opts with pgo_solve  = b; }
    | `Subst       -> { opts with pgo_subst  = b; }
    | `Disjunctive -> { opts with pgo_disjct = b; }

    | `Delta x ->
        { opts with pgo_delta = merged1 opts.pgo_delta (b, x); }

  let merge opts (specs : EcParsetree.ppgoptions) =
    List.fold_left merge1 opts specs
end

module PGInternals = struct
  let pg_cnj_elims = [
    t_elim_false_r   ;
    t_elim_exists_r  ;
    t_elim_and_r     ;
    t_elim_eq_tuple_r;
  ]

  let pg_djn_elims = [
    t_elim_or_r
  ]
end

let t_progress ?options ?ti (tt : FApi.backward) (tc : tcenv1) =
  let options = odfl PGOptions.default options in

  let tt =
    if   options.pgo_solve
    then FApi.t_or (t_assumption `Alpha) tt
    else tt

  and ti = odfl (fun (_ : EcIdent.t) -> t_id) ti in

  let t_progress_subst ?eqid =
    let sk1 = { empty_subst_kind with sk_local = true ; } in
    let sk2 = {  full_subst_kind with sk_local = false; } in
    FApi.t_or (t_subst ~kind:sk1 ?eqid) (t_subst ~kind:sk2 ?eqid)
  in

  let ts =
    if   options.pgo_subst
    then fun id -> FApi.t_or (t_progress_subst ~eqid:id) (ti id)
    else ti in

  (* Entry of progress: simplify goal, and chain with progress *)
  let rec entry tc = FApi.t_seq (t_simplify ~delta:false) aux0 tc

  (* Progress (level 0): try to apply user tactic, chain with level 1. *)
  and aux0 tc = FApi.t_seq (FApi.t_try tt) aux1 tc

  (* Progress (level 1): intro/elim top-level assumption *)
  and aux1 tc =
    let hyps, concl = FApi.tc1_flat tc in

    match sform_of_form concl with
    | SFquant (Lforall, _, _) ->
      let bd  = fst (destr_forall concl) in
      let ids = List.map (EcIdent.name |- fst) bd in
      let ids = LDecl.fresh_ids hyps ids in
      FApi.t_seq (t_intros_i ids) aux0 tc

    | SFlet (LTuple fs, f1, _) ->
      let tys    = List.map snd fs in
      let tc, hd = FApi.bwd1_of_fwd (pf_gen_tuple_elim tys hyps) tc in
      let pt     = { pt_head = PTHandle hd; pt_args = []; } in
      FApi.t_seq (t_elimT_form pt f1) aux0 tc

    | SFimp (_, _) -> begin
      let id = LDecl.fresh_id hyps "H" in

      match t_intros_i_seq [id] tt tc with
      | tc when FApi.tc_done tc -> tc
      | _ ->
          (* FIXME: we'd like to do the following:
             intros id; on_intro id; entry
             on_intro:
               (try subst (if option)
                or default_intro id);
             default_intro id =
               try absurd id;   -- ie if id: b and !b is an assumption
               rewrite_bool id; -- if id: !b -> rewrite b = false,
                                   if id:  b -> rewrite b = true
               default_on_intro id *)
          let iffail tc =
            t_intros_i_seq [id] (FApi.t_seq (ts id) entry) tc in

          let elims = PGInternals.pg_cnj_elims in
          let elims =
            if   options.pgo_disjct
            then PGInternals.pg_djn_elims @ elims
            else elims
          in

          let reduce =
            if options.pgo_delta.pgod_case then `Full else `NoDelta in

          FApi.t_switch ~on:`All (t_elim_r ~reduce elims) ~ifok:aux0 ~iffail tc
    end

    | _ when options.pgo_split ->
       let thesplit =
         match options.pgo_delta.pgod_split with
         | true  -> t_split ~closeonly:false ~reduce:`Full
         | false ->
             FApi.t_or
               (t_split ~reduce:`NoDelta)
               (t_split ~closeonly:true ~reduce:`Full) in

        FApi.t_try (FApi.t_seq thesplit aux0) tc

    | _ -> t_id tc

  in entry tc

(* -------------------------------------------------------------------- *)
(*let pp_tc tc =
  let pr = proofenv_of_proof (proof_of_tcenv tc) in
  let cl = List.map (FApi.get_pregoal_by_id^~ pr) (FApi.tc_opened tc) in
  let cl = List.map (fun x -> (EcEnv.LDecl.tohyps x.g_hyps, x.g_concl)) cl in

  match cl with [] -> () | hd :: tl ->

  Format.eprintf "%a@."
    (EcPrinting.pp_goal (EcPrinting.PPEnv.ofenv (FApi.tc_env tc)))
    (hd, `All tl)
 *)
type cstate = {
  cs_undosubst : Sid.t;
  cs_sbeq : Sid.t;
}

let t_crush ?(delta = true) ?tsolve (tc : tcenv1) =

  let dtsolve =
    [t_assumption `Conv; t_absurd_hyp ~conv:`Conv; t_false ~conv:`Conv] in

  let tsolve = odfl (FApi.t_ors dtsolve) tsolve in

  let tt = FApi.t_try (t_assumption `Alpha) in

 (* let t_print _s t tc = t tc in
    Format.eprintf "%s@." s;
    pp_tc (FApi.tcenv_of_tcenv1 tc);
    t tc in *)

  (* Entry of progress: simplify goal, and chain with progress *)
  let rec entry (st : cstate) = t_simplify ~delta:false @! aux0 st

  (* Progress (level 0): try to apply user tactic. *)
  and aux0 (st : cstate) = FApi.t_try tt @! aux1 st

  (* Progress (level 1): intro/elim top-level assumption. *)
  and aux1 (st : cstate) tc =
    let hyps, concl = FApi.tc1_flat tc in

    match sform_of_form concl with
    | SFquant (Lforall, _, _) ->
      let bd  = fst (destr_forall concl) in
      let ids = List.map (EcIdent.name |- fst) bd in
      let ids = LDecl.fresh_ids hyps ids in
      FApi.t_seqs
        [t_intros_i ids; aux0 st;
         t_generalize_hyps ~clear:`Yes ~missing:true ids]
        tc

    | SFlet (LTuple fs, f1, _) ->
      (* FIXME : does t_elimT_form change the hyps ? *)
      let tys    = List.map snd fs in
      let tc, hd = FApi.bwd1_of_fwd (pf_gen_tuple_elim tys hyps) tc in
      let pt     = { pt_head = PTHandle hd; pt_args = []; } in
      FApi.t_seq (t_elimT_form pt f1) (aux0 st) tc

    | SFimp (_, _) -> begin
      let id1 = LDecl.fresh_id hyps "_" in

      match t_intros_i_seq [id1] tt tc with
      | tc when FApi.tc_done tc -> tc
      | tc ->
          let tc = FApi.as_tcenv1 tc in
          let tc =
            let rw =
              t_rewrite_hyp ~xconv:`AlphaEq ~mode:`Bool ~donot:true
                id1 (`LtoR, None) in
            (    FApi.t_try (t_absurd_hyp ~conv:`AlphaEq ~id:id1)
              @! FApi.t_try (FApi.t_seq (FApi.t_try rw) tt)
              @! t_generalize_hyp ~clear:`Yes id1) tc
          in

          let iffail = t_crush_subst st id1 in
          let elims  = PGInternals.pg_cnj_elims in
          let reduce = if delta then `Full else `NoDelta in

          FApi.t_onall
            (FApi.t_switch ~on:`All ~ifok:(aux0 st) ~iffail (t_elim_r ~reduce elims))
            tc
    end

    | _ ->
       let reduce = if delta then `Full else `NoDelta in
       let thesplit tc = t_split ~closeonly:false ~reduce tc in
       let hyps0 = FApi.tc1_hyps tc in
       let shuffle = List.rev_map fst (LDecl.tohyps (FApi.tc1_hyps tc)).h_local in
       let st_split = { st with cs_undosubst = Sid.of_list shuffle } in
       let tc =
         match FApi.t_try_base (thesplit @! aux0 st_split) tc with
         | `Success tc -> tc
         | `Failure _  -> FApi.t_try tsolve tc in
       let pr = proofenv_of_proof (proof_of_tcenv tc) in
       let cl = List.map (FApi.get_pregoal_by_id^~ pr) (FApi.tc_opened tc) in
       let nl = List.length cl in
       match cl with | [] | [_] -> tc
       | _ :: _ ->
       let concl = f_ands (List.map (fun g -> g.g_concl) cl)  in
       let tc, hd = FApi.newgoal tc ~hyps:hyps0 concl in
       let pt = { pt_head = PTHandle hd; pt_args = []; } in
       let rec t_final n tc =
         if n = 1 then (t_intros_n 1 @! t_assumption `Alpha) tc
         else FApi.t_seqs [t_elim_and; t_intros_n 1; t_final (n-1)] tc in

       FApi.t_on1 nl t_id
         ~ttout:(t_shuffle shuffle @! t_cutdef pt concl @! t_final nl) tc

  and t_crush_subst st eqid tc =
    let togen = ref None in
    let t_subst sk tc =
      let newtc, gen = t_subst_x ~clear:SCnone ~kind:sk ~gen:true ~eqid:eqid ~tg:st.cs_sbeq tc in
      togen := gen;
      newtc in

    let t_init =
      let sk1 = { empty_subst_kind with sk_local = true ; } in
      let sk2 = {  full_subst_kind with sk_local = false; } in
      t_intros_i [eqid] @!
        FApi.t_try (FApi.t_or (t_subst sk1) (t_subst sk2)) in

    let gen_hyps post gG =
      let do1 gG (id, d) =
        match d with
        | LD_var (_ty, Some body) -> f_let1 id body gG
        | LD_var (ty, None)       -> f_forall [id, GTty ty] gG
        | LD_mem mt               -> f_forall_mems [id, mt] gG
        | LD_modty(mt,r)          -> f_forall [id, GTmodty(mt,r)] gG
        | LD_hyp f                -> f_imp f gG
        | LD_abs_st _             -> raise InvalidGoalShape in
      List.fold_left do1 gG post in

    let t_final tc =
      match !togen with
      | None -> t_generalize_hyp ~clear:`Yes ~missing:false eqid tc
      | Some (y, substy, postx, side, var, f) ->
        let ty = f.f_ty in
        let postx =
          List.filter (fun (x,_fx) ->
              Sid.mem x st.cs_undosubst) postx in
        let posty = List.map substy postx in
        if posty = [] then t_clear eqid tc
        else
        let ids = List.rev (List.map fst postx) in
        let gG = FApi.tc1_goal tc in
        let x =
          match var with
          | `Glob (mp,m) -> f_glob mp m
          | `Local x     -> f_local x ty
          | `PVar(x,m)   -> f_pvar x ty m in
        let posty_G = f_lambda [y, GTty ty] (gen_hyps posty gG) in
        let postf_G = f_app posty_G [f] tbool in
        let postx_G = (gen_hyps postx gG) in

        let t_eq_ind =
          (t_apply_s LG.p_eq_ind [ty] ~args:[x;f;posty_G] ~sk:2) @+
            [ if side = `LtoR then t_hyp eqid else t_symmetry @! t_hyp eqid;
              t_id] in

        let t_change f tc =
          FApi.tcenv_of_tcenv1 (t_change f tc) in

        FApi.t_seqs [
          (* pre, x=f, postx{x <- f} |- G *)
          t_generalize_hyps ~clear:`Yes ~missing:false ~letin:true ids;
          (* pre, x=f |- postx{x <- f} => G *)
          t_change postf_G;
          (* pre, x=f |- posty_G f *)
          t_eq_ind;
          (* pre, x=f |- posty_G x *)
          t_change postx_G;
          (* pre, x=f |- postx => G *)
          t_intros_i ids;
          (* hyps0 |- G *)
          t_generalize_hyp ~clear:`Yes ~missing:false eqid] tc
    in
    let entry tc =
      match !togen with
      | None   -> entry { st with cs_sbeq = Sid.add eqid st.cs_sbeq } tc
      | Some _ -> entry st tc in

    FApi.t_seqs [t_init; entry; t_final] tc

  in

  let state =
    { cs_undosubst = Sid.empty;
      cs_sbeq = Sid.of_list (List.map fst (LDecl.tohyps (FApi.tc1_hyps tc)).h_local);
    } in
  FApi.t_seq (entry state) (t_simplify_with_info EcReduction.nodelta) tc


(* -------------------------------------------------------------------- *)
let t_logic_trivial (tc : tcenv1) =
  let seqs = [
    FApi.t_try (t_assumption `Conv);
    t_progress t_id;
    FApi.t_try (t_assumption `Conv);
    FApi.t_try (t_absurd_hyp ~conv:`AlphaEq);
    t_fail;
  ]

  in FApi.t_internal (FApi.t_try (FApi.t_seqs seqs)) tc

(* -------------------------------------------------------------------- *)
let t_trivial ?(subtc : FApi.backward option) (tc : tcenv1) =
  let tryassum  = FApi.t_try (t_assumption `Conv) in
  let tprogress = t_progress t_id in
  let subtc     = subtc |> odfl t_id in
  let seqs      =
    [FApi.t_try (t_false ~conv:`Conv ?id:None);
     tryassum; tprogress; tryassum; subtc; t_logic_trivial; t_fail] in

  FApi.t_internal (FApi.t_try (FApi.t_seqs seqs)) tc

(* -------------------------------------------------------------------- *)
let t_congr (f1, f2) (args, ty) tc =
  let rec doit args ty tc =
    match args with
    | [] -> t_id tc

    | (a1, a2) :: args->
        let aty  = a1.f_ty in
        let m1   = f_app f1 (List.rev_map fst args) (tfun aty ty) in
        let m2   = f_app f2 (List.rev_map snd args) (tfun aty ty) in
        let tcgr = t_apply_s LG.p_fcongr [ty; aty] ~args:[m2; a1; a2] ~sk:1 in

        let tsub tc =
          let fx   = EcIdent.create "f" in
          let fty  = tfun aty ty in
          let body = f_app (f_local fx fty) [a1] ty in
          let lam  = EcFol.f_lambda [(fx, GTty fty)] body in
            FApi.t_sub
              [doit args fty]
              (t_apply_s LG.p_fcongr [ty; fty] ~args:[lam; m1; m2] ~sk:1 tc)
        in
          FApi.t_sub
            [tsub; tcgr]
            (t_transitivity (EcFol.f_app m2 [a1] ty) tc)
  in
  doit (List.rev args) ty tc

(* -------------------------------------------------------------------- *)
type smtmode = [`Standard | `Strict | `Report of EcLocation.t option]

(* -------------------------------------------------------------------- *)
let t_smt ~(mode:smtmode) pi tc =
  let error () =
    match mode with
    | `Standard ->
        tc_error !!tc ~catchable:true  "cannot prove goal"
    | `Strict ->
        tc_error !!tc ~catchable:false "cannot prove goal (strict)"
    | `Report loc ->
        EcEnv.notify (FApi.tc1_env tc) `Critical
          "%s: smt call failed"
          (loc |> omap EcLocation.tostring |> odfl "unknown");
        t_admit tc
  in

  let env, hyps, concl = FApi.tc1_eflat tc in
  let notify = (fun lvl (lazy s) -> EcEnv.notify env lvl "%s" s) in

  if   EcSmt.check ~notify pi hyps concl
  then FApi.xmutate1 tc `Smt []
  else error ()

(* -------------------------------------------------------------------- *)
let t_solve ?(canfail = true) ?(bases = [EcEnv.Auto.dname]) ?(depth = 1) (tc : tcenv1) =
  let bases = EcEnv.Auto.getall bases (FApi.tc1_env tc) in

  let t_apply1 p tc =
    let pt = PT.pt_of_uglobal !!tc (FApi.tc1_hyps tc) p in
    try
      Apply.t_apply_bwd_r ~mode:fmdelta ~canview:false pt tc
    with Apply.NoInstance _ -> t_fail tc in

  let rec t_apply ctn p  =
    if   ctn > depth
    then t_fail
    else t_apply1 p @! t_trivial @! t_solve (ctn + 1) bases

  and t_solve ctn bases =
    match bases with
    | [] -> t_abort
    | p::bases -> FApi.t_or (t_apply ctn p) (t_solve ctn bases) in

  let t = t_solve 0 bases in
  let t = if canfail then FApi.t_try t else t in

  t tc

(* --------------------------------------------------------------------- *)
let t_crush_fwd ?(delta = true) nb_intros (tc : tcenv1) =
  let t_progress_subst ?eqid =
    let sk1 = { empty_subst_kind with sk_local = true ; } in
    let sk2 = {  full_subst_kind with sk_local = false; } in
    FApi.t_or
      (t_subst ~clear:false ~kind:sk1 ?eqid)
      (t_subst ~clear:false ~kind:sk2 ?eqid)
  in

  let tt = FApi.t_try (t_assumption `Alpha) in

  let ts id = FApi.t_try (t_progress_subst ~eqid:id) in

  let rec aux0 (nbi : int) tc =
    FApi.t_seq (FApi.t_try tt) (aux1 nbi) tc

  and aux1 (nbi : int) tc =
    if nbi = 0 || FApi.tc_done (FApi.tcenv_of_tcenv1 tc) then t_id tc
    else

    let hyps, concl = FApi.tc1_flat tc in

    match sform_of_form concl with
    | SFimp (_, _) -> begin
      let id = LDecl.fresh_id hyps "_" in

      match t_intros_i_seq [id] tt tc with
      | tc when FApi.tc_done tc -> tc
      | tc ->
        let tc = FApi.as_tcenv1 tc in
        let tc =
          let rw =
            t_rewrite_hyp ~xconv:`AlphaEq ~mode:`Bool ~donot:true
              id (`LtoR, None) in
            (    FApi.t_try (t_absurd_hyp ~conv:`AlphaEq ~id)
              @! FApi.t_try (FApi.t_seq (FApi.t_try rw) tt)
              @! t_generalize_hyp ~clear:`Yes id) tc
        in

        let incr i = nbi + i - 1 in

        let iffail tc =
          (t_intros_i_seq [id] (ts id) @! aux0 (incr 0)) tc
        in

        let t_elim_false_r f concl tc =
          (t_elim_false_r f concl tc, t_id)

        and t_elim_and_r f concl tc =
          (t_elim_and_r f concl tc, aux0 (incr 2))

        and t_elim_eq_tuple_r f concl tc =
          let n, tc = t_elim_eq_tuple_r_n f concl tc in
          (tc, aux0 (incr n)) in

        let elims  = [ t_elim_false_r; t_elim_and_r; t_elim_eq_tuple_r; ] in
        let reduce = if delta then `Full else `NoDelta in

        FApi.t_onall
          (FApi.t_xswitch ~on:`All ~iffail (t_elim_r ~reduce elims))
          tc
      end

    | _ -> t_fail tc
  in

  FApi.t_seq
    (aux0 nb_intros)
    (t_simplify_with_info EcReduction.nodelta) tc
