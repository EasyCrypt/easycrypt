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
open EcLogic

(* -------------------------------------------------------------------- *)
exception InvalidProofTerm
exception InvalidGoalShape

type side = [`Left|`Right]

(* -------------------------------------------------------------------- *)
exception NoMatch

let t_lazy_match ?(reduce = true) (tx : form -> FApi.backward) (tc : tcenv) =
  let fp = FApi.tc_goal tc in

  try  tx fp tc
  with
  | NoMatch when not reduce -> raise InvalidGoalShape
  | NoMatch -> begin
    let hyps, concl = FApi.tc_flat tc in
    match h_red_opt full_red hyps concl with
    | None    -> raise InvalidGoalShape
    | Some fp -> tx fp tc
  end

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
            let f1    = Fsubst.f_subst sbt f1 in
            let subpt =
              match subpt with
              | None       -> { pt_head = PTCut f1; pt_args = []; }
              | Some subpt -> subpt
            in
            let subpt, subax = check subpt tc in
            if not (EcReduction.is_conv hyps f1 subax) then
              raise InvalidProofTerm;
            ((sbt, f2), PASub (Some subpt))

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
let t_admit (tc : tcenv) = FApi.close tc VAdmit

(* -------------------------------------------------------------------- *)
let t_change (fp : form) (tc : tcenv) =
  let hyps, concl = FApi.tc_flat tc in
  if not (EcReduction.is_conv hyps fp concl) then
    raise InvalidGoalShape;
  FApi.mutate tc (fun hd -> VConv (hd, Sid.empty)) fp

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
  let (tc, hd) = FApi.newgoal tc ~hyps concl in
  FApi.close tc (VIntros (hd, List.map tg_val ids))

(* -------------------------------------------------------------------- *)
let t_intro_i (id : EcIdent.t) (tc : tcenv) =
  t_intros [notag id] tc

(* ------------------------------------------------------------------ *)
let t_apply ?(focus = true) (pt : proofterm) (tc : tcenv) =
  let (hyps, concl) = FApi.tc_flat tc in
  let (pt, ax), tc  = RApi.of_pure tc (fun tc -> LowApply.check pt tc) in

  if not (EcReduction.is_conv hyps concl ax) then
    raise InvalidGoalShape;
  FApi.close tc (VApply pt)

(* -------------------------------------------------------------------- *)
let t_apply_s ?focus (p : path) (tys : ty list) (fs : form list) (n : int) =
  let pt =
    let args = (List.map paformula fs) @ (List.create n (PASub None)) in
    { pt_head = PTGlobal (p, tys); pt_args = args; } in

  fun tc -> t_apply ?focus pt tc

(* -------------------------------------------------------------------- *)
let t_apply_hd ?focus (hd : handle) (fs : form list) (n : int) =
  let pt =
    let args = (List.map paformula fs) @ (List.create n (PASub None)) in
    { pt_head = PTHandle hd; pt_args = args; } in

  fun tc -> t_apply ?focus pt tc

(* -------------------------------------------------------------------- *)
let t_cut (fp : form) (tc : tcenv) =
  (* FIXME: check that Logic is loaded *)
  let concl = FApi.tc_goal tc in
  t_apply_s ~focus:true EcCoreLib.p_cut_lemma [] [fp; concl] 2 tc

(* -------------------------------------------------------------------- *)
let t_true (tc : tcenv) =
  t_apply_s ~focus:true EcCoreLib.p_true [] [] 0 tc

(* -------------------------------------------------------------------- *)
let t_reflex_s (f : form) (tc : tcenv) =
  t_apply_s EcCoreLib.p_eq_refl [f.f_ty] [f] 0 tc

let t_reflex ?reduce (tc : tcenv) =
  let t_reflex_r (fp : form) (tc : tcenv) =
    match sform_of_form fp with
    | SFeq (f1, f2) ->
        if   EcReduction.is_conv (FApi.tc_hyps tc) f1 f2
        then t_reflex_s f1 tc
        else raise NoMatch
    | _ -> raise NoMatch
  in
    t_lazy_match ?reduce t_reflex_r tc

(* -------------------------------------------------------------------- *)
let t_or_intro_s (b : bool) (side : side) (f1, f2 : form pair) (tc : tcenv) =
  let p =
    match side, b with
    | `Left , true  -> EcCoreLib.p_ora_intro_l
    | `Right, true  -> EcCoreLib.p_ora_intro_r
    | `Left , false -> EcCoreLib.p_or_intro_l
    | `Right, false -> EcCoreLib.p_or_intro_r
  in
  t_apply_s ~focus:true p [] [f1; f2] 1 tc

let t_or_intro ?reduce (side : side) (tc : tcenv) =
  let t_or_intro_r (fp : form) (tc : tcenv) =
    match sform_of_form fp with
    | SFor (b, (left, right)) -> t_or_intro_s b side (left, right) tc
    | _ -> raise NoMatch
  in
    t_lazy_match ?reduce t_or_intro_r tc

let t_left  ?reduce tc = t_or_intro ?reduce `Left  tc
let t_right ?reduce tc = t_or_intro ?reduce `Right tc

(* -------------------------------------------------------------------- *)
let t_and_intro_s (b : bool) (f1, f2 : form pair) (tc : tcenv) =
  let p = if b then EcCoreLib.p_anda_intro else EcCoreLib.p_and_intro in
  t_apply_s ~focus:true p [] [f1; f2] 2 tc

let t_and_intro ?reduce (tc : tcenv) =
  let t_and_intro_r (fp : form) (tc : tcenv) =
    match sform_of_form fp with
    | SFand (b, (left, right)) -> t_and_intro_s b (left, right) tc
    | _ -> raise NoMatch
  in
    t_lazy_match ?reduce t_and_intro_r tc

(* -------------------------------------------------------------------- *)
let t_iff_intro_s (f1, f2 : form pair) (tc : tcenv) =
  t_apply_s ~focus:true EcCoreLib.p_iff_intro [] [f1; f2] 2 tc

let t_iff_intro ?reduce (tc : tcenv) =
  let t_iff_intro_r (fp : form) (tc : tcenv) =
    match sform_of_form fp with
    | SFiff (f1, f2) -> t_iff_intro_s (f1, f2) tc
    | _ -> raise NoMatch
  in
    t_lazy_match ?reduce t_iff_intro_r tc

(* -------------------------------------------------------------------- *)
let gen_tuple_intro tys =
  let var ty name i =
    let var = EcIdent.create (Printf.sprintf "%s_%d" name i) in
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
  FApi.newfact pe (VExtern (`TupleCongr tys)) hyps fp

(* -------------------------------------------------------------------- *)
let t_tuple_intro_s (fs : form pair list) (tc : tcenv) =
  let tc  = RApi.rtcenv_of_tcenv tc in
  let tys = List.map (fun f -> (fst f).f_ty) fs in
  let hd  = RApi.bwd_of_fwd (pf_gen_tuple_intro tys (RApi.tc_hyps tc)) tc in
  let fs  = List.flatten (List.map (fun (x, y) -> [x; y]) fs) in

  RApi.to_pure_u tc (t_apply_hd ~focus:true hd fs (List.length tys));
  RApi.tcenv_of_rtcenv tc

let t_tuple_intro ?reduce (tc : tcenv) =
  let t_tuple_intro_r (fp : form) (tc : tcenv) =
    match sform_of_form fp with
    | SFeq (f1, f2) when is_tuple f1 && is_tuple f2 ->
        let fs = List.combine (destr_tuple f1) (destr_tuple f2) in
        t_tuple_intro_s fs tc
    | _ -> raise NoMatch
  in
    t_lazy_match ?reduce t_tuple_intro_r tc

(* -------------------------------------------------------------------- *)
let t_elim_r ?(reduce = true) txs tc =
  match sform_of_form (FApi.tc_goal tc) with
  | SFimp (f1, f2) ->
      let rec aux f1 =
        let sf1 = sform_of_form f1 in

        match
          List.pick (fun tx ->
              try  Some (tx (f1, sf1) f2 tc)
              with NoMatch -> None)
            txs
        with
        | Some gs -> gs
        | None    ->
            if not reduce then raise InvalidGoalShape;
            match h_red_opt full_red (FApi.tc_hyps tc) f1 with
            | None    -> raise InvalidGoalShape
            | Some f1 -> aux f1
      in
        aux f1

    | _ -> raise InvalidGoalShape

(* -------------------------------------------------------------------- *)
let t_elim_false_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFfalse -> t_apply_s ~focus:true EcCoreLib.p_false_elim [] [concl] 0 tc
  | _ -> raise NoMatch

let t_elim_false tc = t_elim_r [t_elim_false_r] tc

(* --------------------------------------------------------------------- *)
let t_elim_and_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFand (b, (a1, a2)) ->
      let p = if b then EcCoreLib.p_anda_elim else EcCoreLib.p_and_elim in
      t_apply_s ~focus:true p [] [a1; a2; concl] 1 tc
  | _ -> raise NoMatch

let t_elim_and goal = t_elim_r [t_elim_and_r] goal

(* --------------------------------------------------------------------- *)
let t_elim_or_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFor (b, (a1, a2)) ->
      let p = if b then EcCoreLib.p_ora_elim else EcCoreLib.p_or_elim  in
      t_apply_s ~focus:true p [] [a1; a2; concl] 2 tc
  | _ -> raise NoMatch

let t_elim_or tc = t_elim_r [t_elim_or_r] tc

(* --------------------------------------------------------------------- *)
let t_elim_iff_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFiff (a1, a2) ->
      t_apply_s ~focus:true EcCoreLib.p_iff_elim [] [a1; a2; concl] 1 tc
  | _ -> raise NoMatch

let t_elim_iff tc = t_elim_r [t_elim_iff_r] tc

(* -------------------------------------------------------------------- *)
let t_elim_if_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFif (a1, a2, a3) ->
      t_apply_s ~focus:true EcCoreLib.p_if_elim [] [a1; a2; a3; concl] 2 tc
  | _ -> raise NoMatch

let t_elim_if tc = t_elim_r [t_elim_if_r] tc

(* -------------------------------------------------------------------- *)
let gen_tuple_elim (tys : ty list) : form =
  let p  = EcIdent.create "p" in
  let fp = f_local p tbool in

  let var ty name i =
    let var = EcIdent.create (Printf.sprintf "%s_%d" name i) in
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
let pf_gen_tuple_elim tys hyps pe =
  let fp = gen_tuple_elim tys in
  FApi.newfact pe (VExtern (`TupleInd tys)) hyps fp

(* -------------------------------------------------------------------- *)
let t_elim_eq_tuple_r ((_, sf) : form * sform) concl tc =
  match sf with
  | SFeq (a1, a2) when is_tuple a1 && is_tuple a2 ->
      let tc   = RApi.rtcenv_of_tcenv tc in
      let hyps = RApi.tc_hyps tc in
      let fs   = List.combine (destr_tuple a1) (destr_tuple a2) in
      let tys  = List.map (f_ty |- fst) fs in
      let hd   = RApi.bwd_of_fwd (pf_gen_tuple_elim tys hyps) tc in
      let args = List.flatten (List.map (fun (x, y) -> [x; y]) fs) in
      let args = concl :: args in

      RApi.to_pure_u tc (t_apply_hd ~focus:true hd args 1);
      RApi.tcenv_of_rtcenv tc

  | _ -> raise NoMatch

let t_elim_eq_tuple goal = t_elim_r [t_elim_eq_tuple_r] goal

(* -------------------------------------------------------------------- *)
let t_elim_exists_r ((f, _) : form * sform) concl tc =
  match f.f_node with
  | Fquant (Lexists, bd, body) ->
      let newc = f_forall bd (f_imp body concl) in
      FApi.mutate tc (fun hd -> VExtern (`Exists hd)) newc
  | _ -> raise NoMatch

let t_elim_exists tc = t_elim_r [t_elim_exists_r] tc

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

let t_elim tc = t_elim_r t_elim_default_r tc

(* -------------------------------------------------------------------- *)
let t_split (tc : tcenv) =
  let t_split_r (fp : form) (tc : tcenv) =
    let hyps, concl = FApi.tc_flat tc in

    match sform_of_form fp with
    | SFtrue ->
        t_true tc
    | SFand (b, (f1, f2)) ->
        t_and_intro_s b (f1, f2) tc
    | SFiff (f1, f2) ->
        t_iff_intro_s (f1, f2) tc
    | SFeq (f1, f2) when EcReduction.is_conv hyps f1 f2 ->
        t_reflex_s f1 tc
    | SFeq (f1, f2) when is_tuple f1 && is_tuple f2 ->
        let fs = List.combine (destr_tuple f1) (destr_tuple f2) in
        t_tuple_intro_s fs tc
(*
    | SFif (cond, _, _) ->
        let tc = if f_equal concl fp then tc else t_change fp tc in
        let tc = t_case cond tc in
          tc
*)

    | _ -> raise NoMatch
  in
    t_lazy_match t_split_r tc

(* -------------------------------------------------------------------- *)
let t_rewrite (pt : proofterm) (pos : ptnpos) (tc : tcenv) =
  let tc = RApi.rtcenv_of_tcenv tc in
  let (hyps, concl) = RApi.tc_flat tc in
  let (pt, ax) = LowApply.check pt tc in

  if not (FPosition.is_empty pos) then begin
    let (left, right) =
      match sform_of_form ax with
      | SFeq  (f1, f2) -> (f1, f2)
      | SFiff (f1, f2) -> (f1, f2)
      | _ -> raise InvalidProofTerm
    in

    let change f =
      if not (EcReduction.is_conv hyps f left) then
        raise InvalidGoalShape;
      right
    in

    let newconcl =
      try  FPosition.map pos change concl
      with InvalidPosition -> raise InvalidGoalShape in

    let hd   = RApi.newgoal tc newconcl in
    let rwpt = { rpt_proof = pt; rpt_occrs = pos; } in

    RApi.close tc (VRewrite (hd, rwpt))
  end;

  RApi.tcenv_of_rtcenv tc
