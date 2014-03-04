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
| PASub     of proofterm option

(* -------------------------------------------------------------------- *)
let paformula x = PAFormula x
let pamemory  x = PAMemory  x
let pamodule  x = PAModule  x

(* -------------------------------------------------------------------- *)
type rwproofterm = {
  rpt_proof : proofterm;
  rpt_occrs : EcMatching.ptnpos;
}

(* -------------------------------------------------------------------- *)
type location = {
  plc_parent : location option;
  plc_name   : string;
  plc_loc    : EcLocation.t;
}

exception TcError of location * string Lazy.t

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
| VSmt                               (* SMT call *)
| VAdmit                             (* admit *)
| VIntros  of (handle * idents)      (* intros *)
| VConv    of (handle * Sid.t)       (* weakening + conversion *)
| VRewrite of (handle * rwproofterm) (* rewrite *)
| VApply   of proofterm              (* modus ponens *)
| VExtern  : 'a -> validation        (* external (hl/phl/prhl/...) proof-node *)

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
let tc_error pe ?loc msg =
  assert false                          (* FIXME *)

(* -------------------------------------------------------------------- *)
let tc_lookup_error pe ?loc kind qs =
  assert false                          (* FIXME *)

(* -------------------------------------------------------------------- *)
module FApi = struct
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
  let tc_flat (tc : tcenv) =
    let { g_hyps; g_concl } = current tc in (g_hyps, g_concl)

  (* ------------------------------------------------------------------ *)
  let tc_eflat (tc : tcenv) =
    let (hyps, concl) = tc_flat tc in
      (LDecl.toenv hyps, hyps, concl)

  (* ------------------------------------------------------------------ *)
  let tc_penv (tc : tcenv) = tc.tce_proofenv
  let tc_hyps (tc : tcenv) = fst (tc_flat tc)
  let tc_goal (tc : tcenv) = snd (tc_flat tc)

  (* ------------------------------------------------------------------ *)
  let penv_of_tcenv (tc : tcenv) =
    tc.tce_proofenv

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
  let pf_newgoal (pe : proofenv) ?vx hyps concl =
    let hid     = ID.gen () in
    let pregoal = { g_uid = hid; g_hyps = hyps; g_concl = concl; } in
    let goal    = { g_goal = pregoal; g_validation = vx; } in
    let pe      = { pe with pr_goals = ID.Map.add pregoal.g_uid goal pe.pr_goals; } in
      (pe, pregoal)

  (* ------------------------------------------------------------------ *)
  let newgoal (tc : tcenv) ?(hyps : LDecl.hyps option) (concl : form) =
    let hyps     = ofdfl (fun () -> tc_hyps tc) hyps in
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
      (tc, pg.g_uid)

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
    { tc with tce_subgoals =
        push_closed_to_tcenvx current.g_uid tc.tce_subgoals }

  (* ------------------------------------------------------------------ *)
  let mutate (tc : tcenv) (vx : handle -> validation) (fp : form) =
    (* FIXME: create on direct left *)
    let (tc, hd) = newgoal tc fp in close tc (vx hd)

  (* ------------------------------------------------------------------ *)
  let newfact (pe : proofenv) vx hyps concl =
    snd_map (fun x -> x.g_uid) (pf_newgoal pe ~vx:vx hyps concl)

  (* ------------------------------------------------------------------ *)
  let bwd_of_fwd (tx : forward) (tc : tcenv) =
    let (pe, hd) = tx tc.tce_proofenv in
    ({ tc with tce_proofenv = pe }, hd)

  (* ------------------------------------------------------------------ *)
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
let (!!) = FApi.tc_penv

(* -------------------------------------------------------------------- *)
module RApi = struct
  type rproofenv = proofenv ref
  type rtcenv    = tcenv ref

  (* ------------------------------------------------------------------ *)
  let rtcenv_of_tcenv (tc :  tcenv) : rtcenv = ref tc
  let tcenv_of_rtcenv (tc : rtcenv) :  tcenv = !tc

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
  let to_pure (tc : rtcenv) (tx :tcenv -> tcenv * 'a) =
    reffold (fun tc -> swap (tx tc)) tc

  (* ------------------------------------------------------------------ *)
  let to_pure_u (tc : rtcenv) (tx :tcenv -> tcenv) : unit =
    tc := tx !tc

  (* ------------------------------------------------------------------ *)
  let newgoal pe ?hyps concl =
    reffold (fun pe -> swap (FApi.newgoal pe ?hyps concl)) pe

  (* ------------------------------------------------------------------ *)
  let close tc validation =
    tc := FApi.close !tc validation

  (* ------------------------------------------------------------------ *)
  let bwd_of_fwd (tx : FApi.forward) (tc : rtcenv) =
    reffold (fun tc -> swap (FApi.bwd_of_fwd tx tc)) tc

  (* ------------------------------------------------------------------ *)
  let pf_get_pregoal_by_id id pf = FApi.get_pregoal_by_id id !pf
  let tc_get_pregoal_by_id id pf = FApi.get_pregoal_by_id id (!pf).tce_proofenv

  (* ------------------------------------------------------------------ *)
  let tc_penv  (tc : rtcenv) = FApi.tc_penv  !tc
  let tc_flat  (tc : rtcenv) = FApi.tc_flat  !tc
  let tc_eflat (tc : rtcenv) = FApi.tc_eflat !tc
  let tc_goal  (tc : rtcenv) = FApi.tc_goal  !tc
  let tc_hyps  (tc : rtcenv) = FApi.tc_hyps  !tc
end

type rproofenv = RApi.rproofenv
type rtcenv    = RApi.rtcenv

(* -------------------------------------------------------------------- *)
let tcenv_of_proof (pf : proof) =
  let tcenv =
    { tce_proofenv = pf.pr_env;
      tce_goal     = None;
      tce_subgoals = { tcec_closed = ID.Set.empty;
                       tcec_gzip   = { tcez_left  = [];
                                       tcez_right = pf.pr_opened;
                                       tcez_ctxt  = `Top; } } }
  in
    FApi.down_tcenv (FApi.reduce_tcenv tcenv)

(* -------------------------------------------------------------------- *)
let proof_of_tcenv (tc : tcenv) =
  let tc  = FApi.reduce_tcenv (FApi.uptop_tcenv tc) in
  let rg  = tc.tce_subgoals.tcec_gzip.tcez_right in
  let lg  = tc.tce_subgoals.tcec_gzip.tcez_left  in
  let fg  = tc.tce_goal |> omap (fun g -> g.g_uid) in

    { pr_env    = tc.tce_proofenv;
      pr_opened = List.rev_append lg (List.ocons fg rg); }

(* -------------------------------------------------------------------- *)
let start (hyps : LDecl.hyps) (goal : form) =
  let uid = ID.gen () in
  let hid = ID.gen () in

  let goal = { g_uid = hid; g_hyps = hyps; g_concl = goal; } in
  let goal = { g_goal = goal; g_validation = None; } in
  let env  = { pr_uid   = uid;
               pr_main  = hid;
               pr_goals = ID.Map.singleton hid goal; } in

    { pr_env = env; pr_opened = [hid]; }

(* -------------------------------------------------------------------- *)
let opened (pf : proof) =
  match pf.pr_opened with
  | [] -> None
  | hd :: _ -> Some (List.length pf.pr_opened,
                     FApi.get_pregoal_by_id hd pf.pr_env)

(* -------------------------------------------------------------------- *)
module Exn = struct
  (* FIXME: cast-and-reraise *)
  let recast pe f x = f x

  let recast_pe pe f =
    recast pe f ()

  let recast_tc tc f =
    let penv = FApi.penv_of_tcenv tc in
    let hyps, _concl = FApi.tc_flat tc in
      recast_pe penv (fun () -> f hyps)
end

(* -------------------------------------------------------------------- *)
module TcTyping = struct
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
  let pf_check_tvi (pe : proofenv) typ tvi =
    match tvi with
    | None -> ()

    | Some (EcUnify.TVIunamed tyargs) ->
        if List.length tyargs <> List.length typ then
          tc_error pe
            (Printf.sprintf
               "wrong number of type parameters (%d, expecting %d)"
               (List.length tyargs) (List.length typ))

    | Some (EcUnify.TVInamed tyargs) ->
        let typnames = List.map (EcIdent.name |- fst) typ in
        List.iter
          (fun (x, _) ->
            if not (List.mem x typnames) then
              tc_error pe ("unknown type variable: " ^ x))
          tyargs
end
