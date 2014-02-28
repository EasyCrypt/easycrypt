(* -------------------------------------------------------------------- *)
open EcUtils
open EcFol
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
let t_admit (tc : tcenv) = FApi.close tc VAdmit

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm

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

(* ------------------------------------------------------------------ *)
let t_apply (pt : proofterm) (tc : tcenv) =
  let (hyps, concl) = FApi.tc_flat tc in
  let (pt, ax), tc  = RApi.of_pure tc (fun tc -> LowApply.check pt tc) in

  if not (EcReduction.is_conv hyps concl ax) then
    raise InvalidProofTerm;
  FApi.close tc (VApply pt)
