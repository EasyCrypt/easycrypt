(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcIdent
open EcParsetree
open EcTypes
open EcFol
open EcEnv

module L = EcLocation

(* -------------------------------------------------------------------- *)
module ID : sig
  type id = private int

  val gen : unit -> id

  module Map : EcMaps.Map.S with type key   = id
  module Set : EcMaps.Set.S with type M.key = id
end = struct
  type id = int

  let gen () = EcUid.unique ()

  module Map = EcMaps.Mint
  module Set = EcMaps.Sint
end

(* -------------------------------------------------------------------- *)
type handle = ID.id

(* -------------------------------------------------------------------- *)
type proofterm = { pt_head : pt_head; pt_args : pt_arg list; }

and pt_head =
| PTCut    of EcFol.form
| PTHandle of handle
| PTLocal  of EcIdent.t
| PTGlobal of EcPath.path * (ty list)

and pt_arg =
| PAFormula of EcFol.form
| PAMemory  of EcMemory.memory
| PAModule  of (EcPath.mpath * EcModules.module_sig)
| PASub     of proofterm

(* -------------------------------------------------------------------- *)
type position

type rwproofterm = {
  rpt_proof : proofterm;
  rtp_occrs : position list;
}

(* -------------------------------------------------------------------- *)
type location = {
  plc_parent : location option;
  plc_name   : string;
  plc_loc    : EcLocation.t;
}

exception TcError of location * string Lazy.t

let tcerror (lc : location) (msg : string) =
  raise (TcError (lc, lazy msg))

(* -------------------------------------------------------------------- *)
type proof = {
  pr_env    : proofenv;
  pr_opened : handle list;
}

and proofenv = {
  pr_uid   : ID.id;          (* unique ID for this proof *)
  pr_main  : ID.id;          (* top goal, contains the final result *)
  pr_goals : goal ID.Map.t;  (* set of all goals, closed and opened *)
}

and pregoal = {
  g_uid   : handle;                     (* this goal ID *)
  g_hyps  : LDecl.hyps;                 (* goal local environment *)
  g_concl : form;                       (* goal conclusion *)
}

and goal = {
  g_goal       : pregoal;
  g_validation : validation option;
}

and validation =
| VSmt     : validation                 (* SMT call *)
| VAdmit   : validation                 (* admit *)
| VConv    : Sid.t -> validation        (* weakening + conversion *)
| VApply   : proofterm -> validation    (* modus ponens *)
| VRewrite : rwproofterm -> validation  (* rewrite *)
| VExtern  : 'a -> validation           (* external (hl/phl/prhl/...) proof-node *)

and tcenv = {
  tce_proofenv   : proofenv;           (* top-level proof environment *)
  tce_goal       : pregoal option;     (* current goal *)
  tce_subgoals   : tcenv_ctxt;         (* subgoals (zipper) *)
}

and tcenv_ctxt = {
  tcec_closed : ID.Set.t;
  tcec_gzip   : tcenv_gzip;
}

and tcenv_gzip = {
  tcez_left  : handle list;
  tcez_right : handle list;
  tcez_ctxt  : [`Top | `Intern of tcenv_gzip];
}

(* -------------------------------------------------------------------- *)
let (++) (pe : proofenv) (_l : EcLocation.t) =
  pe                                    (* FIXME *)

(* -------------------------------------------------------------------- *)
let pf_tcerror pe msg =
  assert false                          (* FIXME *)

(* -------------------------------------------------------------------- *)
let tc_lookup_error pe ?loc kind qs =
  assert false                          (* FIXME *)

let tc_pterm_apperror pe ?loc kind =
  assert false

(* -------------------------------------------------------------------- *)
module Api = struct
  type forward  = proofenv -> proofenv * handle
  type backward = tcenv -> tcenv
  type mixward  = tcenv -> tcenv * handle

  exception InvalidStateException of string

  (* ------------------------------------------------------------------ *)
  let get_goal_by_id (hd : handle) (pe : proofenv) =
    match ID.Map.find_opt hd pe.pr_goals with
    | None    -> raise (InvalidStateException "goal-map-inconsistent")
    | Some pr -> pr

  (* ------------------------------------------------------------------ *)
  let get_pregoal_by_id (hd : handle) (pe : proofenv) =
    (get_goal_by_id hd pe).g_goal

  (* ------------------------------------------------------------------ *)
  let update_goal_map (tx : goal -> goal) (hd : handle) (pe : proofenv) =
    let change g =
      match g with
      | None   -> raise (InvalidStateException "goal-map-inconsistent")
      | Some g -> Some (tx g)
    in
      { pe with pr_goals = ID.Map.change change hd pe.pr_goals }

  (* ------------------------------------------------------------------ *)
  let update_goal_map_on_tcenv (tx : goal -> goal) (hd : handle) (tc : tcenv) =
    { tc with tce_proofenv = update_goal_map tx hd tc.tce_proofenv }

  (* ------------------------------------------------------------------ *)
  let check_tcenv_opened (tc : tcenv) =
    if tc.tce_goal = None then
      raise (InvalidStateException "all-goals-closed")

  (* ------------------------------------------------------------------ *)
  let current (tc : tcenv) =
    check_tcenv_opened tc; EcUtils.oget (tc.tce_goal)

  (* ------------------------------------------------------------------ *)
  let current_flat (tc : tcenv) =
    let { g_hyps; g_concl } = current tc in (g_hyps, g_concl)

  (* ------------------------------------------------------------------ *)
  let current_hyps (tc : tcenv) =
    fst (current_flat tc)

  (* ------------------------------------------------------------------ *)
  let penv_of_tcenv (tc : tcenv) = tc.tce_proofenv

  (* ------------------------------------------------------------------ *)
  let reduce_tcenvx (tcx : tcenv_ctxt) =
    if ID.Set.is_empty tcx.tcec_closed then
      tcx
    else
      let filter =
        List.fold_right
          (fun id (ids, gs) ->
            if   ID.Set.mem id ids
            then (ID.Set.remove id ids, gs)
            else (ids, id :: gs))
      in

      let ids = tcx.tcec_closed in
      let ids, tcez_left  = filter tcx.tcec_gzip.tcez_left  (ids, []) in
      let ids, tcez_right = filter tcx.tcec_gzip.tcez_right (ids, []) in
        { tcec_closed = ids;
          tcec_gzip   = { tcx.tcec_gzip with tcez_left; tcez_right; } }

  (* ------------------------------------------------------------------ *)
  let pop_from_tcenvx (tcx : tcenv_ctxt) =
    let tcx = reduce_tcenvx tcx in
    let tcz = tcx.tcec_gzip in

    let (sg, tcz) =
      match tcz.tcez_right with
      | sg :: rgs -> (Some sg, { tcz with tcez_right = rgs })
      | [] ->
          match tcz.tcez_left with
          | sg :: lgs -> (Some sg, { tcz with tcez_left = lgs })
          | [] -> (None, tcz)
    in
      (sg, { tcx with tcec_gzip = tcz })

  (* -------------------------------------------------------------------- *)
  let reduce_tcenv (tc : tcenv) =
    match tc.tce_goal with
    | None ->
        let (sg, tcx) = pop_from_tcenvx tc.tce_subgoals in

        { tc with
            tce_goal     = sg |> omap (get_pregoal_by_id^~ tc.tce_proofenv);
            tce_subgoals = tcx; }

    | Some _ ->
        { tc with tce_subgoals = reduce_tcenvx tc.tce_subgoals }

  (* ------------------------------------------------------------------ *)
  let up_tcenvx (tcx : tcenv_ctxt) =
    let tcz = tcx.tcec_gzip in
    let tcz =
      match tcz.tcez_ctxt with
      | `Top -> raise (InvalidStateException "at-top")
      | `Intern subtcz ->
          { tcez_left  = tcz.tcez_left @ subtcz.tcez_left;
            tcez_right = subtcz.tcez_right @ tcz.tcez_right;
            tcez_ctxt  = subtcz.tcez_ctxt; }
    in
      { tcx with tcec_gzip = tcz }

  (* ------------------------------------------------------------------ *)
  let down_tcenvx (tcx : tcenv_ctxt) =
    let tcz =
      { tcez_left  = [];
        tcez_right = [];
        tcez_ctxt  = `Intern tcx.tcec_gzip; } in

      { tcx with tcec_gzip = tcz }

  (* ------------------------------------------------------------------ *)
  let up_tcenv (tc : tcenv) =
    let tc = { tc with tce_subgoals = up_tcenvx tc.tce_subgoals } in
      reduce_tcenv tc

  (* ------------------------------------------------------------------ *)
  let uptop_tcenv (tc : tcenv) =
    let rec doit tcx =
      match tcx.tcec_gzip.tcez_ctxt with
      | `Top      -> tcx
      | `Intern _ -> doit (up_tcenvx tcx)
    in

    let tc = { tc with tce_subgoals = doit tc.tce_subgoals } in
      reduce_tcenv tc

  (* ------------------------------------------------------------------ *)
  let down_tcenv (tc : tcenv) =
    { tc with tce_subgoals = down_tcenvx tc.tce_subgoals }

  (* ------------------------------------------------------------------ *)
  let push_closed_to_tcenvx (hd : handle) (tcx : tcenv_ctxt) =
    { tcx with tcec_closed = ID.Set.add hd tcx.tcec_closed }

  (* ------------------------------------------------------------------ *)
  let start (hyps : LDecl.hyps) (goal : form) =
    let uid = ID.gen () in
    let hid = ID.gen () in

    let goal = { g_uid = hid; g_hyps = hyps; g_concl = goal; } in
    let goal = { g_goal = goal; g_validation = None; } in
    let env  = { pr_uid   = uid;
                 pr_main  = hid;
                 pr_goals = ID.Map.singleton hid goal; } in

      { pr_env = env; pr_opened = [hid]; }

  (* ------------------------------------------------------------------ *)
  let focused (pf : proof) =
    match pf.pr_opened with
    | [] -> None
    | hd :: _ -> Some (List.length pf.pr_opened, get_pregoal_by_id hd pf.pr_env)

  (* ------------------------------------------------------------------ *)
  let pf_newgoal (pe : proofenv) (hyps : LDecl.hyps) (concl : form) =
    let hid     = ID.gen () in
    let pregoal = { g_uid = hid; g_hyps = hyps; g_concl = concl; } in
    let goal    = { g_goal = pregoal; g_validation = None; } in
    let pe      = { pe with pr_goals = ID.Map.add pregoal.g_uid goal pe.pr_goals; } in
      (pe, pregoal)

  (* ------------------------------------------------------------------ *)
  let newgoal (tc : tcenv) ?(hyps : LDecl.hyps option) (concl : form) =
    let hyps     = ofdfl (fun () -> current_hyps tc) hyps in
    let (pe, pg) = pf_newgoal tc.tce_proofenv hyps concl in

    let tc = { tc with tce_proofenv = pe; } in
    let tc =
      match tc.tce_goal with
      | None   -> { tc with tce_goal = Some pg }
      | Some _ ->
          let tcz = tc.tce_subgoals in
          let tcz =
            { tcz with tcec_gzip =
                { tcz.tcec_gzip with tcez_right =
                    tcz.tcec_gzip.tcez_right @ [pg.g_uid] } }
          in
            { tc with tce_subgoals = tcz }
    in
      (pg.g_uid, tc)

  (* ------------------------------------------------------------------ *)
  let close (tc : tcenv) (vx : validation) =
    let current = current tc in

    let change g =
      if g.g_validation <> None || g.g_goal != current then
        raise (InvalidStateException "goal-map-inconsistent");
      { g with g_validation = Some vx }
    in

    (* Close current goal, set focused goal to None *)
    let tc = update_goal_map_on_tcenv change current.g_uid tc in
    let tc = { tc with tce_goal = None } in

    (* Maybe pop one opened goal from proof context *)
    let tc = reduce_tcenv tc in

    (* Register current goal has being closed *)
    { tc with tce_subgoals = push_closed_to_tcenvx current.g_uid tc.tce_subgoals }

  (* Tacticals *)
  type ontest    = int -> proofenv -> handle -> bool
  type direction = [ `Left | `Right ]

  let on (tt : backward) (f : ontest) (tc : tcenv) =
    assert false

  let first (tt : backward) (i : int) (tc : tcenv) =
    assert false

  let last (tt : backward) (i : int) (tc : tcenv) =
    assert false

  let rotate (d : direction) (i : int) (tc : tcenv) =
    assert false

  let seq (tt1 : backward) (tt2 : backward) (tc : tcenv) =
    tt2 (tt1 tc)

  let rec lseq (tts : backward list) (tc : tcenv) =
    match tts with
    | []       -> tc
    | t :: tts -> seq t (lseq tts) tc
end

(* -------------------------------------------------------------------- *)
module RApi : sig
  type rproofenv
  type rtcenv

  val of_pure : tcenv -> (rtcenv -> 'a) -> 'a * tcenv

  val newgoal : rtcenv -> ?hyps:LDecl.hyps -> form -> handle

  val pf_get_goal_by_id    : handle -> rproofenv -> goal
  val pf_get_pregoal_by_id : handle -> rproofenv -> pregoal

  val tc_get_goal_by_id    : handle -> rtcenv -> goal
  val tc_get_pregoal_by_id : handle -> rtcenv -> pregoal

  val current_hyps : rtcenv -> LDecl.hyps

  val freeze  : rtcenv -> rtcenv
  val restore : dst:rtcenv -> src:rtcenv -> unit
end = struct
  type rproofenv = proofenv ref
  type rtcenv    = tcenv ref

  (* ------------------------------------------------------------------ *)
  let freeze (pe : rtcenv) =
    ref !pe

  let restore ~(dst:rtcenv) ~(src:rtcenv) =
    dst := !src

  (* ------------------------------------------------------------------ *)
  let of_pure (tc : tcenv) (tx : rtcenv -> 'a) =
    let rtc  = ref tc in
    let aout = tx rtc in
    (aout, !rtc)

  (* ------------------------------------------------------------------ *)
  let newgoal pe ?hyps concl =
    reffold (fun pe -> Api.newgoal pe ?hyps concl) pe

  (* ------------------------------------------------------------------ *)
  let pf_get_pregoal_by_id id pf = Api.get_pregoal_by_id id !pf
  let pf_get_goal_by_id    id pf = Api.get_goal_by_id    id !pf

  let tc_get_pregoal_by_id id pf = Api.get_pregoal_by_id id (!pf).tce_proofenv
  let tc_get_goal_by_id    id pf = Api.get_goal_by_id    id (!pf).tce_proofenv

  (* ------------------------------------------------------------------ *)
  let current_hyps (tc : rtcenv) = Api.current_hyps !tc
end

type rproofenv = RApi.rproofenv
type rtcenv    = RApi.rtcenv

(* -------------------------------------------------------------------- *)
module LowLevel = struct
  let t_admit (tc : tcenv) =
    Api.close tc VAdmit
end

(* -------------------------------------------------------------------- *)
module LowApply = struct
  (* ------------------------------------------------------------------ *)
  exception InvalidProofTerm

  (* ------------------------------------------------------------------ *)
  let rec check_pthead (pt : pt_head) (tc : rtcenv) =
    match pt with
    | PTCut f ->
        (* cut - create a dedicated subgoal *)
        let handle = RApi.newgoal tc f in (PTHandle handle, f)

    | PTHandle hd ->
        (* proof reuse - fetch corresponding subgoal*)
        let subgoal = RApi.tc_get_pregoal_by_id hd tc in
        if subgoal.g_hyps !=(*φ*) RApi.current_hyps tc then
          raise InvalidProofTerm;
        (pt, subgoal.g_concl)

    | PTLocal x -> begin
        let hyps = RApi.current_hyps tc in
        try  (pt, LDecl.lookup_hyp_by_id x hyps)
        with LDecl.Ldecl_error _ -> raise InvalidProofTerm
    end

    | PTGlobal (p, tys) ->
        (* FIXME: poor API ==> poor error recovery *)
        let env = LDecl.toenv (RApi.current_hyps tc) in
        (pt, EcEnv.Ax.instanciate p tys env)

  (* ------------------------------------------------------------------ *)
  and check (pt : proofterm) (tc : rtcenv) =
    let hyps = RApi.current_hyps tc in
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

  (* ------------------------------------------------------------------ *)
  let t_apply (pt : proofterm) (tc : tcenv) =
    let (hyps, concl) = Api.current_flat tc in
    let (pt, ax), tc  = RApi.of_pure tc (fun tc -> check pt tc) in

    if not (EcReduction.is_conv hyps concl ax) then
      raise InvalidProofTerm;
    Api.close tc (VApply pt)
end

(* -------------------------------------------------------------------- *)
module Exn : sig
  val recast_pe : proofenv -> (unit -> 'a) -> 'a
  val recast_tc : tcenv -> (LDecl.hyps -> 'a) -> 'a
end = struct
  (* FIXME: cast-and-reraise *)
  let recast pe f x = f x

  let recast_pe pe f =
    recast pe f ()

  let recast_tc tc f =
    let penv = Api.penv_of_tcenv tc in
    let hyps, _concl = Api.current_flat tc in
      recast_pe penv (fun () -> f hyps)
end

(* -------------------------------------------------------------------- *)
module Typing : sig
  val unienv_of_hyps : LDecl.hyps -> EcUnify.unienv

  (* Typing in the environment implied by [LDecl.hyps]. *)
  val process_form_opt : LDecl.hyps -> pformula -> ty option -> form
  val process_form     : LDecl.hyps -> pformula -> ty -> form
  val process_formula  : LDecl.hyps -> pformula -> form

  (* Typing in the [LDecl.hyps] implied by the proof env.
   * Typing exceptions are recasted in the proof env. context *)
  val pf_process_form_opt : proofenv -> LDecl.hyps -> pformula -> ty option -> form
  val pf_process_form     : proofenv -> LDecl.hyps -> pformula -> ty -> form
  val pf_process_formula  : proofenv -> LDecl.hyps -> pformula -> form

  (* Typing in the [proofenv] implies for the [tcenv].
   * Typing exceptions are recasted in the proof env. context *)
  val tc_process_form_opt : tcenv -> pformula -> ty option -> form
  val tc_process_form     : tcenv -> pformula -> ty -> form
  val tc_process_formula  : tcenv -> pformula -> form

  (* FIXME: factor out this to the typing module *)
  val pf_check_tvi : proofenv -> (EcIdent.t * 'a) list -> EcUnify.tvi -> unit
end = struct
  open EcBaseLogic

  (* ------------------------------------------------------------------ *)
  let unienv_of_hyps hyps =
     let tv = (LDecl.tohyps hyps).h_tvar in
       EcUnify.UniEnv.create (Some tv)

  (* ------------------------------------------------------------------ *)
  let process_form_opt hyps pf oty =
    let ue  = unienv_of_hyps hyps in
    let ff  = EcTyping.trans_form_opt (LDecl.toenv hyps) ue pf oty in
      EcFol.Fsubst.uni (EcUnify.UniEnv.close ue) ff

  let process_form hyps pf ty =
    process_form_opt hyps pf (Some ty)

  let process_formula hyps pf =
    process_form hyps pf tbool

  (* ------------------------------------------------------------------ *)
  let pf_process_form_opt pe hyps pf oty =
    Exn.recast_pe pe (fun () -> process_form_opt hyps pf oty)

  let pf_process_form pe hyps pf ty =
    Exn.recast_pe pe (fun () -> process_form hyps pf ty)

  let pf_process_formula pe hyps pf =
    Exn.recast_pe pe (fun () -> process_formula hyps pf)

  (* ------------------------------------------------------------------ *)
  let tc_process_form_opt tc pf oty =
    Exn.recast_tc tc (fun hyps -> process_form_opt hyps pf oty)

  let tc_process_form tc pf ty =
    Exn.recast_tc tc (fun hyps -> process_form hyps pf ty)

  let tc_process_formula tc pf =
    Exn.recast_tc tc (fun hyps -> process_formula hyps pf)

  (* ------------------------------------------------------------------ *)
  (* FIXME: factor out to typing module                                 *)
  (* FIXME: TC HOOK - check parameter constraints                       *)
  (* ------------------------------------------------------------------ *)
  let pf_check_tvi pe typ tvi =
    match tvi with
    | None -> ()

    | Some (EcUnify.TVIunamed tyargs) ->
        if List.length tyargs <> List.length typ then
          pf_tcerror pe
            (Printf.sprintf
               "wrong number of type parameters (%d, expecting %d)"
               (List.length tyargs) (List.length typ))

    | Some (EcUnify.TVInamed tyargs) ->
        let typnames = List.map (EcIdent.name |- fst) typ in
        List.iter
          (fun (x, _) ->
            if not (List.mem x typnames) then
              pf_tcerror pe ("unknown type variable: " ^ x))
          tyargs
end

(* -------------------------------------------------------------------- *)
module ProofTerm : sig
  type evmap = form EcMetaProg.evmap

  type pt_env = {
    pte_pe : proofenv;         (* proofenv of this proof-term *)
    pte_hy : LDecl.hyps;       (* local context *)
    pte_ue : EcUnify.unienv;   (* unification env. *)
    pte_ev : evmap ref;        (* metavar env. *)
  }

  type pt_ev = {
    ptev_env : pt_env;
    ptev_pt  : proofterm;
    ptev_ax  : form;
  }

  type pt_ev_arg = {
    ptea_env : pt_env;
    ptea_arg : pt_ev_arg_r;
  }

  and pt_ev_arg_r =
  | PVAFormula of EcFol.form
  | PVAMemory  of EcMemory.memory
  | PVAModule  of (EcPath.mpath * EcModules.module_sig)
  | PVASub     of pt_ev

  (* Proof-terms typing *)
  val process_pterm          : pt_env -> pformula fpattern_kind -> pt_ev
  val process_pterm_arg      : pt_ev  -> fpattern_arg located -> pt_ev_arg
  val process_pterm_args_app : pt_ev  -> fpattern_arg located list -> pt_ev
  val process_full_pterm     : pt_env -> ffpattern -> pt_ev

  (* Proof-terms tying in backward tactics *)
  val tc_process_full_pterm : tcenv -> ffpattern -> pt_ev

  (* Proof-terms manipulation *)
  val apply_pterm_to_arg  : pt_ev -> pt_ev_arg -> pt_ev
  val apply_pterm_to_hole : pt_ev -> pt_ev

  (* pattern matching - raise [MatchFailure] on failure. *)
  val pf_form_match : pt_env -> ptn:form -> form -> unit
  val pf_unify      : pt_env -> ty -> ty -> unit

  (* Proof-terms concretization, i.e. evmap/unienv resolution *)
  val can_concretize : pt_env -> bool
  val concretize     : pt_ev  -> proofterm * form
end = struct
  type evmap = form EcMetaProg.evmap

  type pt_env = {
    pte_pe : proofenv;
    pte_hy : LDecl.hyps;
    pte_ue : EcUnify.unienv;
    pte_ev : evmap ref;
  }

  type pt_ev = {
    ptev_env : pt_env;
    ptev_pt  : proofterm;
    ptev_ax  : form;
  }

  type pt_ev_arg = {
    ptea_env : pt_env;
    ptea_arg : pt_ev_arg_r;
  }

  and pt_ev_arg_r =
  | PVAFormula of EcFol.form
  | PVAMemory  of EcMemory.memory
  | PVAModule  of (EcPath.mpath * EcModules.module_sig)
  | PVASub     of pt_ev

  (* -------------------------------------------------------------------- *)
  let ptenv_of_tcenv (tc : tcenv) =
    { pte_pe = tc.tce_proofenv;
      pte_hy = Api.current_hyps tc;
      pte_ue = Typing.unienv_of_hyps (Api.current_hyps tc);
      pte_ev = ref EcMetaProg.EV.empty; }

  (* -------------------------------------------------------------------- *)
  let pf_form_match (pt : pt_env) ~ptn subject =
    try
      let (ue, ev) =
        EcMetaProg.f_match_core EcMetaProg.fmrigid pt.pte_hy
          (pt.pte_ue, !(pt.pte_ev)) ~ptn subject
      in
        EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue;
        pt.pte_ev := ev
    with EcMetaProg.MatchFailure as exn ->
      (* FIXME: should we check for empty inters. with ecmap? *)
      if not (EcReduction.is_conv pt.pte_hy ptn subject) then
        raise exn

  (* -------------------------------------------------------------------- *)
  let pf_unify (pt : pt_env) ty1 ty2 =
    let ue = EcUnify.UniEnv.copy pt.pte_ue in
      EcUnify.unify (LDecl.toenv pt.pte_hy) ue ty1 ty2;
      EcUnify.UniEnv.restore ~dst:pt.pte_ue ~src:ue

  (* -------------------------------------------------------------------- *)
  let rec pmsymbol_of_pform fp : pmsymbol option =
    match unloc fp with
    | PFident ({ pl_desc = (nm, x); pl_loc = loc }, _) when EcIo.is_mod_ident x ->
        Some (List.map (fun nm1 -> (mk_loc loc nm1, None)) (nm @ [x]))

    | PFapp ({ pl_desc = PFident ({ pl_desc = (nm, x); pl_loc = loc }, _) },
             [{ pl_desc = PFtuple args; }]) -> begin

      let mod_ = List.map (fun nm1 -> (mk_loc loc nm1, None)) nm in
      let args =
        List.map
          (fun a -> pmsymbol_of_pform a |> omap (mk_loc a.pl_loc))
          args
      in

        match List.exists (fun x -> x = None) args with
        | true  -> None
        | false ->
            let args = List.map (fun a -> oget a) args in
              Some (mod_ @ [mk_loc loc x, Some args])
    end

    | PFtuple [fp] -> pmsymbol_of_pform fp

    | _ -> None

  (* ------------------------------------------------------------------ *)
  let lookup_named_psymbol (hyps : LDecl.hyps) ~hastyp fp =
    match fp with
    | ([], x) when LDecl.has_hyp x hyps && not hastyp ->
        let (x, fp) = LDecl.lookup_hyp x hyps in
          Some (`Local x, ([], fp))

    | _ ->
      match EcEnv.Ax.lookup_opt fp (LDecl.toenv hyps) with
      | Some (p, ({ EcDecl.ax_spec = Some fp } as ax)) ->
          Some (`Global p, (ax.EcDecl.ax_tparams, fp))
      | _ -> None

  (* -------------------------------------------------------------------- *)
  let process_named_pterm pe (tvi, fp) =
    let env = LDecl.toenv pe.pte_hy in

    let (p, (typ, ax)) =
      match lookup_named_psymbol pe.pte_hy ~hastyp:(tvi <> None) (unloc fp) with
      | Some (p, ax) -> (p, ax)
      | None -> tc_lookup_error pe.pte_pe `Lemma (unloc fp)
    in

    let tvi =
      Exn.recast_pe pe.pte_pe
        (fun () -> omap (EcTyping.transtvi env pe.pte_ue) tvi)
    in

    Typing.pf_check_tvi pe.pte_pe typ tvi;

    (* FIXME: TC HOOK *)
    let fs  = EcUnify.UniEnv.opentvi pe.pte_ue typ tvi in
    let ax  = Fsubst.subst_tvar fs ax in
    let typ = List.map (fun (a, _) -> EcIdent.Mid.find a fs) typ in

    (p, (typ, ax))

  (* ------------------------------------------------------------------ *)
  let process_pterm pe pt =
    let (pt, ax) =
      match pt with
      | FPNamed (fp, tyargs) -> begin
          match process_named_pterm pe (tyargs, fp) with
          | (`Local  x, ([] , ax)) -> (PTLocal  x, ax)
          | (`Global p, (typ, ax)) -> (PTGlobal (p, typ), ax)

          | _ -> assert false
      end

    | FPCut fp ->
        let fp = Typing.pf_process_formula pe.pte_pe pe.pte_hy fp in
          (PTCut fp, fp)
    in

    let pt = { pt_head = pt; pt_args = []; } in

    { ptev_env = pe; ptev_pt = pt; ptev_ax = ax; }

  (* ------------------------------------------------------------------ *)
  let trans_pterm_arg_impl pe f =
    let pt = { pt_head = PTCut f; pt_args = []; } in
    let pt = { ptev_env = pe; ptev_pt = pt; ptev_ax = f; } in
      { ptea_env = pe; ptea_arg = PVASub pt; }

  (* ------------------------------------------------------------------ *)
  let trans_pterm_arg_value pe ?name { pl_desc = arg } =
    match arg with
    | EA_mod _ | EA_mem _ -> tc_pterm_apperror pe.pte_pe `FormWanted

    | EA_none ->
        let aty = EcUnify.UniEnv.fresh pe.pte_ue in
        let x   = EcIdent.create (odfl "x" name) in
          pe.pte_ev := EcMetaProg.EV.add x !(pe.pte_ev);
          { ptea_env = pe; ptea_arg = PVAFormula (f_local x aty); }

    | EA_form fp ->
        let env = LDecl.toenv pe.pte_hy in
        let fp  = (fun () -> EcTyping.trans_form_opt env pe.pte_ue fp None) in
        let fp  = Exn.recast_pe pe.pte_pe fp in
          { ptea_env = pe; ptea_arg = PVAFormula fp; }

  (* ------------------------------------------------------------------ *)
  let trans_pterm_arg_mod pe arg =
    let mp =
      match unloc arg with
      | EA_none    -> tc_pterm_apperror pe.pte_pe `CannotInfer
      | EA_mem _   -> tc_pterm_apperror pe.pte_pe `ModuleWanted
      | EA_mod mp  -> mp
      | EA_form fp ->
        match pmsymbol_of_pform fp with
        | None    -> tc_pterm_apperror pe.pte_pe `ModuleWanted
        | Some mp -> mk_loc arg.pl_loc mp
    in

    let env  = LDecl.toenv pe.pte_hy in
    let mod_ = (fun () -> EcTyping.trans_msymbol env mp) in
    let mod_ = Exn.recast_pe pe.pte_pe mod_ in

      { ptea_env = pe; ptea_arg = PVAModule mod_; }

  (* ------------------------------------------------------------------ *)
  let trans_pterm_arg_mem pe { pl_desc = arg } =
    match arg with
    | EA_none -> tc_pterm_apperror pe.pte_pe `CannotInfer
    | EA_mod _ | EA_form _ -> tc_pterm_apperror pe.pte_pe `MemoryWanted

    | EA_mem mem ->
        let env = LDecl.toenv pe.pte_hy in
        let mem = Exn.recast_pe pe.pte_pe (fun () -> EcTyping.transmem env mem) in
          { ptea_env = pe; ptea_arg = PVAMemory mem; }

  (* ------------------------------------------------------------------ *)
  let process_pterm_arg ({ ptev_env = pe } as pt) arg =
    match EcLogic.destruct_product pe.pte_hy pt.ptev_ax with
    | None -> tc_pterm_apperror pe.pte_pe `NotFunctional

    | Some (`Imp (f, _)) -> begin
        match unloc arg with
        | EA_none -> trans_pterm_arg_impl pe f
        | _       -> tc_pterm_apperror pe.pte_pe `PTermWanted
    end

    | Some (`Forall (x, xty, _)) -> begin
        match xty with
        | GTty ty -> trans_pterm_arg_value pe ~name:(EcIdent.name x) arg
        | GTmodty (mt, mr) -> trans_pterm_arg_mod pe arg
        | GTmem mem -> trans_pterm_arg_mem pe arg
    end

  (* -------------------------------------------------------------------- *)
  let hole_for_impl  pe f = trans_pterm_arg_impl  pe f
  let hole_for_mem   pe   = trans_pterm_arg_mem   pe (L.mk_loc L._dummy EA_none)
  let hole_for_mod   pe   = trans_pterm_arg_mod   pe (L.mk_loc L._dummy EA_none)
  let hole_for_value pe   = trans_pterm_arg_value pe (L.mk_loc L._dummy EA_none)

  (* -------------------------------------------------------------------- *)
  let dfl_arg_for_impl  pe f arg = ofdfl (fun () -> hole_for_impl  pe f) arg
  let dfl_arg_for_mem   pe   arg = ofdfl (fun () -> hole_for_mem   pe  ) arg
  let dfl_arg_for_mod   pe   arg = ofdfl (fun () -> hole_for_mod   pe  ) arg
  let dfl_arg_for_value pe   arg = ofdfl (fun () -> hole_for_value pe  ) arg

  (* -------------------------------------------------------------------- *)
  let apply_pterm_to_oarg ({ ptev_env = pe; ptev_pt = rawpt; } as pt) oarg =
    let env = LDecl.toenv pe.pte_hy in
    assert (odfl true (oarg |> omap (fun arg -> pe == arg.ptea_env)));
    match EcLogic.destruct_product pe.pte_hy pt.ptev_ax with
    | None   -> tc_pterm_apperror pe.pte_pe `NotFunctional
    | Some t ->
        let (newax, newarg) =
          match t with
          | `Imp (f1, f2) -> begin
              match (dfl_arg_for_impl pe f1 oarg).ptea_arg with
              | PVASub arg -> begin
                try
                  pf_form_match pe ~ptn:arg.ptev_ax f1;
                  (f2, PASub arg.ptev_pt)
                with EcMetaProg.MatchFailure ->
                  tc_pterm_apperror pe.pte_pe `InvalidArgProof
              end
              | _ -> tc_pterm_apperror pe.pte_pe `PTermWanted
          end

          | `Forall (x, GTty xty, f) -> begin
              match (dfl_arg_for_value pe oarg).ptea_arg with
              | PVAFormula arg -> begin
                try
                  pf_unify pe xty arg.f_ty;
                  (Fsubst.f_subst_local x arg f, PAFormula arg)
                with EcUnify.UnificationFailure _ ->
                  tc_pterm_apperror pe.pte_pe `InvalidArgForm
              end
              | _ -> tc_pterm_apperror pe.pte_pe `FormWanted
          end

          | `Forall (x, GTmem _, f) -> begin
              match (dfl_arg_for_mem pe oarg).ptea_arg with
              | PVAMemory arg -> (Fsubst.f_subst_mem x arg f, PAMemory arg)
              | _ -> tc_pterm_apperror pe.pte_pe `MemoryWanted
          end

          | `Forall (x, GTmodty (emt, restr), f) -> begin
              match (dfl_arg_for_mod pe oarg).ptea_arg with
              | PVAModule (mp, mt) ->
                  (* FIXME: [check_modtype_restr/check_module_in] have awful interfaces! *)
                  EcLogic.check_modtype_restr env mp mt emt restr;
                  EcPV.check_module_in env mp emt;
                  (Fsubst.f_subst_mod x mp f, PAModule (mp, mt))
              | _ -> tc_pterm_apperror pe.pte_pe `ModuleWanted
          end
        in

        let rawargs = rawpt.pt_args @ [newarg] in
        { pt with ptev_ax = newax; ptev_pt = { rawpt with pt_args = rawargs } }

  (* -------------------------------------------------------------------- *)
  let apply_pterm_to_arg pt arg =
    apply_pterm_to_oarg pt (Some arg)

  (* -------------------------------------------------------------------- *)
  let apply_pterm_to_hole pt =
    apply_pterm_to_oarg pt None

  (* -------------------------------------------------------------------- *)
  let process_pterm_arg_app pt arg =
    apply_pterm_to_arg pt (process_pterm_arg pt arg)

  (* -------------------------------------------------------------------- *)
  let process_pterm_args_app pt args =
    List.fold_left process_pterm_arg_app pt args

  (* -------------------------------------------------------------------- *)
  let process_full_pterm pe pf =
    let pt = process_pterm pe pf.fp_kind in
      process_pterm_args_app pt pf.fp_args

  (* -------------------------------------------------------------------- *)
  let tc_process_full_pterm (tc : tcenv) (ff : ffpattern) =
    process_full_pterm (ptenv_of_tcenv tc) ff

  (* -------------------------------------------------------------------- *)
  let can_concretize (pt : pt_env) =
       EcUnify.UniEnv.closed pt.pte_ue
    && EcMetaProg.EV.filled  !(pt.pte_ev)

  (* -------------------------------------------------------------------- *)
  let concretize ({ ptev_env = pe } as pt) =
    assert (can_concretize pe);

    let tysubst = { ty_subst_id with ts_u = EcUnify.UniEnv.close pe.pte_ue } in
    let subst   =
      EcMetaProg.EV.fold
        (fun x f s -> Fsubst.f_bind_local s x f) !(pe.pte_ev)
        (Fsubst.f_subst_init false Mid.empty tysubst EcPath.Mp.empty)
    in

    let onform f = Fsubst.f_subst subst f in

    let rec onpthead = function
      | PTCut    f        -> PTCut (onform f)
      | PTHandle h        -> PTHandle h
      | PTLocal  x        -> PTLocal  x
      | PTGlobal (p, tys) -> PTGlobal (p, List.map (ty_subst tysubst) tys)

    and onptarg = function
      | PAFormula f        -> PAFormula (onform f)
      | PAMemory  m        -> PAMemory m
      | PAModule  (mp, ms) -> PAModule (mp, ms)
      | PASub     pt       -> PASub (onpt pt)

    and onpt { pt_head; pt_args } =
      { pt_head = onpthead pt_head;
        pt_args = List.map onptarg pt_args; }

    in
      (onpt pt.ptev_pt, onform pt.ptev_ax)
end

(* -------------------------------------------------------------------- *)
module HiApply = struct
  (* ------------------------------------------------------------------ *)
  module PT = ProofTerm

  (* ------------------------------------------------------------------ *)
  let process_apply (ff : ffpattern) (tc : tcenv) =
    let module E = struct exception NoInstance end in

    let (hyps, concl) = Api.current_flat tc in

    let rec instantiate istop pt =
      match istop && ProofTerm.can_concretize pt.PT.ptev_env with
      | true ->
          if   EcReduction.is_conv hyps pt.PT.ptev_ax concl
          then pt
          else instantiate false pt

      | false ->
          try
            ProofTerm.pf_form_match pt.PT.ptev_env ~ptn:pt.PT.ptev_ax concl;
            if not (ProofTerm.can_concretize pt.PT.ptev_env) then
              raise E.NoInstance;
            pt
          with EcMetaProg.MatchFailure ->
            match EcLogic.destruct_product hyps pt.PT.ptev_ax with
            | None   -> raise E.NoInstance
            | Some _ ->
                (* FIXME: add internal marker *)
                instantiate true (ProofTerm.apply_pterm_to_hole pt) in

    let pt  = instantiate true (ProofTerm.tc_process_full_pterm tc ff) in
    let pt  = fst (ProofTerm.concretize pt) in

    LowApply.t_apply pt tc
end

(* -------------------------------------------------------------------- *)
module HiLevel = struct
  open EcParsetree

  (* ------------------------------------------------------------------ *)
  let tcenv_of_proof (pf : proof) =
    let tcenv =
      { tce_proofenv = pf.pr_env;
        tce_goal     = None;
        tce_subgoals = { tcec_closed = ID.Set.empty;
                         tcec_gzip   = { tcez_left  = [];
                                         tcez_right = pf.pr_opened;
                                         tcez_ctxt  = `Top; } } }
    in
      Api.down_tcenv (Api.reduce_tcenv tcenv)

  (* ------------------------------------------------------------------ *)
  let proof_of_tcenv (tc : tcenv) =
    let tc  = Api.reduce_tcenv (Api.uptop_tcenv tc) in
    let rg  = tc.tce_subgoals.tcec_gzip.tcez_right in
    let lg  = tc.tce_subgoals.tcec_gzip.tcez_left  in
    let fg  = tc.tce_goal |> omap (fun g -> g.g_uid) in

      { pr_env    = tc.tce_proofenv;
        pr_opened = List.rev_append lg (List.ocons fg rg); }

  (* ------------------------------------------------------------------ *)
  let apply1 (t : ptactic) (tc : tcenv) =
    match (unloc t.pt_core) with
    | Padmit  -> LowLevel.t_admit tc
    | Plogic (Papply (ff, None)) -> HiApply.process_apply ff tc

    | _ -> assert false

  (* ------------------------------------------------------------------ *)
  let apply (t : ptactic list) (pf : proof) =
    let pf = tcenv_of_proof pf in
    let pf = Api.lseq (List.map apply1 t) pf in
      proof_of_tcenv pf
end
