(* -------------------------------------------------------------------- *)
open EcUtils
open EcLocation
open EcIdent
open EcSymbols
open EcTypes
open EcFol
open EcEnv
open EcMatching
open EcReduction
open EcCoreGoal

open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm

(* -------------------------------------------------------------------- *)
module LowApply = struct
  (* ------------------------------------------------------------------ *)
  let rec check_pthead (pt : pt_head) (tc : rtcenv) =
    match pt with
    | PTCut f ->
        (* cut - create a dedicated subgoal *)
        let handle = RApi.newgoal tc f in (PTHandle handle, f)

    | PTHandle hd ->
        (* proof reuse - fetch corresponding subgoal*)
        let subgoal = RApi.tc_get_pregoal_by_id hd tc in
        if subgoal.g_hyps !=(*φ*) RApi.tc_hyps tc then
          raise InvalidProofTerm;
        (pt, subgoal.g_concl)

    | PTLocal x -> begin
        let hyps = RApi.tc_hyps tc in
        try  (pt, LDecl.lookup_hyp_by_id x hyps)
        with LDecl.Ldecl_error _ -> raise InvalidProofTerm
    end

    | PTGlobal (p, tys) ->
        (* FIXME: poor API ==> poor error recovery *)
        let env = LDecl.toenv (RApi.tc_hyps tc) in
        (pt, EcEnv.Ax.instanciate p tys env)

  (* ------------------------------------------------------------------ *)
  and check (pt : proofterm) (tc : rtcenv) =
    let hyps = RApi.tc_hyps tc in
    let env  = LDecl.toenv hyps in

    let rec check_arg (sbt, ax) arg =
      match EcLogic.destruct_product hyps ax with
      | None   -> raise InvalidProofTerm
      | Some t ->
        match t, arg with
        | `Imp (f1, f2), PASub subpt ->
            let f1 = Fsubst.f_subst sbt f1 in
            let subpt, subax = check subpt tc in
            if not (EcReduction.is_conv hyps f1 subax) then
              raise InvalidProofTerm;
            ((sbt, f2), PASub subpt)

        | `Forall (x, xty, f), _ ->
          let xty = Fsubst.gty_subst sbt xty in
          let (sbt, ax) =
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
                EcLogic.check_modtype_restr env mp mt emt restr;
                EcPV.check_module_in env mp emt;
                (Fsubst.f_bind_mod sbt x mp, f)
              with _ -> raise InvalidProofTerm
            end

            | _ -> raise InvalidProofTerm
          in
            ((sbt, ax), arg)

        | _ -> raise InvalidProofTerm
    in

    let (nhd, ax) = check_pthead pt.pt_head tc in
    let (sbt, ax) = (Fsubst.f_subst_id, ax) in
    let (sbt, ax), nargs = List.map_fold check_arg (sbt, ax) pt.pt_args in

    ({ pt_head = nhd; pt_args = nargs }, Fsubst.f_subst sbt ax)
end

(* -------------------------------------------------------------------- *)
module LowIntro = struct
  let valid_value_name (x : symbol) = x <> "_" && EcIo.is_sym_ident x
  let valid_mod_name   (x : symbol) = x <> "_" && EcIo.is_mem_ident x
  let valid_mem_name   (x : symbol) = x <> "_" && EcIo.is_mod_ident x

  type kind = [`Value | `Module | `Memory]

  let tc_no_product (_ : proofenv) ?loc () =
    ignore loc; assert false

  let check_name_validity _pe _kind _x : unit = assert false
end

(* -------------------------------------------------------------------- *)
let t_intros (ids : ident mloc list) (tc : tcenv) =
  let add_local id sbt x gty =
    let gty = Fsubst.gty_subst sbt gty in
    let name = tg_map EcIdent.name id in
    let id   = tg_val id in

    match gty with
    | GTty ty ->
        LowIntro.check_name_validity !!tc `Value name;
        (LD_var (ty, None), Fsubst.f_bind_local sbt x (f_local id ty))
    | GTmem me ->
        LowIntro.check_name_validity !!tc `Memory name;
        (LD_mem me, Fsubst.f_bind_mem sbt x id)
    | GTmodty (i, r) ->
        LowIntro.check_name_validity !!tc `Module name;
        (LD_modty (i, r), Fsubst.f_bind_mod sbt x (EcPath.mident id))
  in

  let add_ld id ld hyps =
    set_oloc
      (tg_tag id)
      (fun () -> LDecl.add_local (tg_val id) ld hyps) ()
  in

  let rec intro1 ((hyps, concl), sbt) id =
    match EcFol.sform_of_form concl with
    | SFquant (Lforall, (x, gty), concl) ->
        let (ld, sbt) = add_local id sbt x gty in
        let hyps = add_ld id ld hyps in
        (hyps, concl), sbt

    | SFimp (prem, concl) ->
        let prem = Fsubst.f_subst sbt prem in
        let hyps = add_ld id (LD_hyp prem) hyps in
        (hyps, concl), sbt

    | SFlet (LSymbol (x, xty), xe, concl) ->
        let xty  = sbt.fs_ty xty in
        let xe   = Fsubst.f_subst sbt xe in
        let sbt  = Fsubst.f_bind_local sbt x (f_local (tg_val id) xty) in
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

  let (hyps, concl), _ =
    List.fold_left intro1 (FApi.tc_flat tc, Fsubst.f_subst_id) ids in
  let (hd, tc) = FApi.newgoal tc ~hyps concl in
  FApi.close tc (VIntros (hd, List.map tg_val ids))

(* -------------------------------------------------------------------- *)
let t_intro_i (id : EcIdent.t) (tc : tcenv) =
  t_intros [notag id] tc

(* -------------------------------------------------------------------- *)
let t_admit (tc : tcenv) = FApi.close tc VAdmit

(* ------------------------------------------------------------------ *)
let t_apply (pt : proofterm) (tc : tcenv) =
  let (hyps, concl) = FApi.tc_flat tc in
  let (pt, ax), tc  = RApi.of_pure tc (fun tc -> LowApply.check pt tc) in

  if not (EcReduction.is_conv hyps concl ax) then
    raise InvalidProofTerm;
  FApi.close tc (VApply pt)

(* -------------------------------------------------------------------- *)
let t_rewrite (pt : proofterm) (pos : ptnpos) (tc : tcenv) =
  let tc = RApi.rtcenv_of_tcenv tc in
  let (hyps, concl) = RApi.tc_flat tc in

  if not (FPosition.is_empty pos) then begin
    let (pt, ax) = LowApply.check pt tc in
    let (left, right) =
      match sform_of_form ax with
      | SFeq  (f1, f2) -> (f1, f2)
      | SFiff (f1, f2) -> (f1, f2)
      | _ -> raise InvalidProofTerm
    in

    let change f =
      if not (EcReduction.is_conv hyps f left) then
        raise InvalidProofTerm;
      right
    in

    let newconcl =
      try  FPosition.map pos change concl
      with InvalidPosition -> raise InvalidProofTerm in

    let hd   = RApi.newgoal tc newconcl in
    let rwpt = { rpt_proof = pt; rpt_occrs = pos; } in

    RApi.close tc (VRewrite (hd, rwpt))
  end;

  RApi.tcenv_of_rtcenv tc
