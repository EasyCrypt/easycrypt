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

  (* external (hl/phl/prhl/...) proof-node *)
| VExtern  : 'a * handle list -> validation

and tcenv1 = {
  tce_penv : proofenv;               (* top-level proof environment *)
  tce_ctxt : tcenv_ctxt;             (* context *)
  tce_goal : pregoal option;         (* current goal *)
}

and tcenv = {
  tce_tcenv : tcenv1;
  tce_goals : tcenv_ctxt1;
}

and tcenv_ctxt  = tcenv_ctxt1 list
and tcenv_ctxt1 = handle list

(* -------------------------------------------------------------------- *)
let tc_error pe ?loc msg =
  assert false                          (* FIXME *)

(* -------------------------------------------------------------------- *)
let tc_lookup_error pe ?loc kind qs =
  assert false                          (* FIXME *)

(* -------------------------------------------------------------------- *)
module FApi = struct
  type forward  = proofenv -> proofenv * handle
  type backward = tcenv1 -> tcenv
  type tactical = tcenv -> tcenv

  exception InvalidStateException of string

  (* ------------------------------------------------------------------ *)
  let get_goal_by_id (hd : handle) (pe : proofenv) =
    match ID.Map.find_opt hd pe.pr_goals with
    | None    -> raise (InvalidStateException "goal-map-inconsistent")
    | Some pr -> pr

  (* ------------------------------------------------------------------ *)
  let tc1_get_goal_by_id (hd : handle) (tc : tcenv1) =
    get_goal_by_id hd tc.tce_penv

  (* ------------------------------------------------------------------ *)
  let tc_get_goal_by_id (hd : handle) (tc : tcenv) =
    get_goal_by_id hd tc.tce_tcenv.tce_penv

  (* ------------------------------------------------------------------ *)
  let get_pregoal_by_id (hd : handle) (pe : proofenv) =
    (get_goal_by_id hd pe).g_goal

  (* ------------------------------------------------------------------ *)
  let tc1_get_pregoal_by_id (hd : handle) (tc : tcenv1) =
    (tc1_get_goal_by_id hd tc).g_goal

  (* ------------------------------------------------------------------ *)
  let tc_get_pregoal_by_id (hd : handle) (tc : tcenv) =
    (tc_get_goal_by_id hd tc).g_goal

  (* ------------------------------------------------------------------ *)
  let update_goal_map (tx : goal -> goal) (hd : handle) (pe : proofenv) =
    let change g =
      match g with
      | None   -> raise (InvalidStateException "goal-map-inconsistent")
      | Some g -> Some (tx g)
    in
      { pe with pr_goals = ID.Map.change change hd pe.pr_goals }

  (* ------------------------------------------------------------------ *)
  let tc1_update_goal_map (tx : goal -> goal) (hd : handle) (tc : tcenv1) =
    { tc with tce_penv = update_goal_map tx hd tc.tce_penv }

  (* ------------------------------------------------------------------ *)
  let tc_update_tcenv (tx : tcenv1 -> tcenv1) (tc : tcenv) =
    { tc with tce_tcenv = tx tc.tce_tcenv }

  (* ------------------------------------------------------------------ *)
  let tc_normalize (tc : tcenv) =
    match tc.tce_tcenv.tce_goal with
    | Some _ -> tc
    | None   ->
        match tc.tce_goals with
        | [] -> tc
        | hd :: tcx1 ->
            let goal = tc_get_pregoal_by_id hd tc in
            { tc with
                tce_tcenv = { tc.tce_tcenv with tce_goal = Some goal };
                tce_goals = tcx1; }

  (* ------------------------------------------------------------------ *)
  let tcenv_of_tcenv1 (tc : tcenv1) =
    { tce_tcenv = tc; tce_goals = []; }

  (* ------------------------------------------------------------------ *)
  let tcenv1_of_penv ?ctxt (hd : handle) (pe : proofenv) =
    let gl = get_pregoal_by_id hd pe in
    { tce_penv = pe; tce_goal = Some gl; tce_ctxt = odfl [] ctxt; }

  (* ------------------------------------------------------------------ *)
  let tcenv_of_penv ?ctxt (hds : handle list) (pe : proofenv) =
    let tc = { tce_penv = pe; tce_goal = None; tce_ctxt = odfl [] ctxt; } in
    let tc = { tce_tcenv = tc; tce_goals = hds; } in
    tc_normalize tc

  (* ------------------------------------------------------------------ *)
  let tc1_check_opened (tc : tcenv1) =
    if tc.tce_goal = None then
      raise (InvalidStateException "all-goals-closed")

  (* ------------------------------------------------------------------ *)
  let tc1_current (tc : tcenv1) =
    tc1_check_opened tc; EcUtils.oget (tc.tce_goal)

  (* ------------------------------------------------------------------ *)
  let tc1_flat (tc : tcenv1) =
    let { g_hyps; g_concl } = tc1_current tc in (g_hyps, g_concl)

  (* ------------------------------------------------------------------ *)
  let tc1_eflat (tc : tcenv1) =
    let (hyps, concl) = tc1_flat tc in
      (LDecl.toenv hyps, hyps, concl)

  (* ------------------------------------------------------------------ *)
  let tc1_penv (tc : tcenv1) = tc.tce_penv
  let tc1_hyps (tc : tcenv1) = fst (tc1_flat tc)
  let tc1_goal (tc : tcenv1) = snd (tc1_flat tc)

  (* ------------------------------------------------------------------ *)
  let tc_flat  (tc : tcenv) = tc1_flat  tc.tce_tcenv
  let tc_eflat (tc : tcenv) = tc1_eflat tc.tce_tcenv
  let tc_penv  (tc : tcenv) = tc1_penv  tc.tce_tcenv
  let tc_hyps  (tc : tcenv) = tc1_hyps  tc.tce_tcenv
  let tc_goal  (tc : tcenv) = tc1_goal  tc.tce_tcenv

  (* ------------------------------------------------------------------ *)
  let tc_opened (tc : tcenv) =
    let goal = tc.tce_tcenv.tce_goal |> omap (fun g -> g.g_uid) in
    List.ocons goal tc.tce_goals

  (* ------------------------------------------------------------------ *)
  let tc_up (tc : tcenv) =
    match tc.tce_tcenv.tce_ctxt with
    | [] -> raise (InvalidStateException "goal-at-top")
    | tcx1 :: tcx ->
        let tc =
          { tc with
              tce_tcenv = { tc.tce_tcenv with tce_ctxt = tcx };
              tce_goals = tc.tce_goals @ tcx1; }
        in tc_normalize tc

  (* ------------------------------------------------------------------ *)
  let tc_uptop (tc : tcenv) =
    let rec doit tc =
      match tc.tce_tcenv.tce_ctxt with
      | [] -> tc
      | _  -> doit (tc_up tc)
    in

    tc_normalize (doit tc)

  (* ------------------------------------------------------------------ *)
  let tc_down (tc : tcenv) =
    let tcenv = tc.tce_tcenv in
    let tcenv = { tcenv with tce_ctxt = tc.tce_goals :: tcenv.tce_ctxt } in
    tcenv

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
    let (pe, pg) = pf_newgoal (tc_penv tc) hyps concl in

    let tc = tc_update_tcenv (fun te -> { te with tce_penv = pe }) tc in
    let tc = { tc with tce_goals = tc.tce_goals @ [pg.g_uid] } in

    (tc_normalize tc, pg.g_uid)

  (* ------------------------------------------------------------------ *)
  let tc1_close (tc : tcenv1) (vx : validation) =
    let current = tc1_current tc in

    let change g =
      if g.g_validation <> None || g.g_goal != current then
        raise (InvalidStateException "goal-map-inconsistent");
      { g with g_validation = Some vx }
    in

    (* Close current goal, set focused goal to None *)
    let tc = tc1_update_goal_map change current.g_uid tc in
    let tc = { tc with tce_goal = None } in

    tc

  (* ------------------------------------------------------------------ *)
  let close (tc : tcenv) (vx : validation) =
    let tc = { tc with tce_tcenv = tc1_close tc.tce_tcenv vx } in
    (* Maybe pop one opened goal from proof context *)
    tc_normalize tc

  (* ------------------------------------------------------------------ *)
  let mutate (tc : tcenv) (vx : handle -> validation) (fp : form) =
    let (tc, hd) = newgoal tc fp in close tc (vx hd)

  (* ------------------------------------------------------------------ *)
  let mutate1 (tc : tcenv1) (vx : handle -> validation) (fp : form) =
    let tc = mutate (tcenv_of_tcenv1 tc) vx fp in
    assert (tc.tce_goals = []); tc.tce_tcenv

  (* ------------------------------------------------------------------ *)
  let xmutate (tc : tcenv) (vx : 'a) (fp : form list) =
    let (tc, hds) = List.map_fold (fun tc fp -> newgoal tc fp) tc fp in
    close tc (VExtern (vx, hds))

  (* ------------------------------------------------------------------ *)
  let newfact (pe : proofenv) vx hyps concl =
    snd_map (fun x -> x.g_uid) (pf_newgoal pe ~vx:vx hyps concl)

  (* ------------------------------------------------------------------ *)
  let bwd1_of_fwd (tx : forward) (tc : tcenv1) =
    let (pe, hd) = tx (tc1_penv tc) in
    ({ tc with tce_penv = pe }, hd)

  (* ------------------------------------------------------------------ *)
  let bwd_of_fwd (tx : forward) (tc : tcenv) =
    let (pe, hd) = tx (tc_penv tc) in
    ({ tc with tce_tcenv = { tc.tce_tcenv with tce_penv = pe } }, hd)

  (* ------------------------------------------------------------------ *)
  (* Tacticals *)
  type direction = [ `Left | `Right ]

  let t_focus (tt : backward) (tc : tcenv) =
    tc_up (tt (tc_down tc))

  let on_sub_goals (tt : backward) (hds : handle list) (pe : proofenv) =
    let do1 pe hd =
      let tc = tt (tcenv1_of_penv hd pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      (tc_penv tc, tc_opened tc) in
    List.map_fold do1 pe hds

  let t_onall (tt : backward) (tc : tcenv) =
    let pe      = tc.tce_tcenv.tce_penv in
    let pe, ln  = on_sub_goals tt (tc_opened tc) pe in
    let ln      = List.flatten ln in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt ln pe

  let t_firsts (tt : backward) (i : int) (tc : tcenv) =
    if i < 0 then invalid_arg "EcCoreGoal.firsts";
    let (ln1, ln2) = List.take_n i (tc_opened tc) in
    let pe, ln1    = on_sub_goals tt ln1 tc.tce_tcenv.tce_penv in
    let handles    = (List.flatten (ln1 @ [ln2])) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  let t_lasts (tt : backward) (i : int) (tc : tcenv) =
    if i < 0 then invalid_arg "EcCoreGoal.firsts";
    let handles    = tc_opened tc in
    let nhandles   = List.length handles in
    let (ln1, ln2) = List.take_n (max 0 (nhandles-i)) handles in
    let pe, ln2    = on_sub_goals tt ln2 tc.tce_tcenv.tce_penv in
    let handles = (List.flatten (ln1 :: ln2)) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  let t_first (tt : backward) (tc : tcenv) = t_firsts tt 1 tc
  let t_last  (tt : backward) (tc : tcenv) = t_lasts  tt 1 tc

  let t_rotate (d : direction) (i : int) (tc : tcenv) =
    let mrev = match d with `Left -> identity | `Right -> List.rev in

    match tc.tce_tcenv.tce_goal with
    | None   -> tc
    | Some g ->
        match List.rotate d (max i 0) (tc_opened tc) with
        | 0, _ -> tc
        | _, s ->
            let tcenv = { tc.tce_tcenv with tce_goal = None; } in
            let tc    = { tc with tce_goals = s; tce_tcenv = tcenv; } in
            tc_normalize tc

  let t_seq (tt1 : backward) (tt2 : backward) (tc : tcenv1) =
    t_onall tt2 (tt1 tc)

  let t_seqs (tts : backward list) (tc : tcenv1) =
    List.fold_left (fun tc tt -> t_onall tt tc) (tcenv_of_tcenv1 tc) tts
end

(* -------------------------------------------------------------------- *)
let (!!) = FApi.tc1_penv
let (!@) = FApi.tcenv_of_tcenv1

(* -------------------------------------------------------------------- *)
module RApi = struct
  type rproofenv = proofenv ref
  type rtcenv    = tcenv    ref

  (* ------------------------------------------------------------------ *)
  let rtcenv_of_tcenv (tc :  tcenv) : rtcenv = ref tc
  let tcenv_of_rtcenv (tc : rtcenv) :  tcenv = !tc

  (* ------------------------------------------------------------------ *)
  let rtcenv_of_tcenv1 (tc : tcenv1) =
    ref (FApi.tcenv_of_tcenv1 tc)

  (* ------------------------------------------------------------------ *)
  let freeze (pe : rtcenv) =
    ref !pe

  (* ------------------------------------------------------------------ *)
  let restore ~(dst:rtcenv) ~(src:rtcenv) =
    dst := !src

  (* ------------------------------------------------------------------ *)
  let of_pure_u (tx : tcenv -> tcenv) (tc : rtcenv) =
    tc := tx !tc

  (* ------------------------------------------------------------------ *)
  let to_pure_u (tx : rtcenv -> unit) (tc : tcenv) =
    let tc = ref tc in tx tc; !tc

  (* ------------------------------------------------------------------ *)
  let of_pure (tx : tcenv -> 'a * tcenv) (tc : rtcenv) =
    reffold tx tc

  (* ------------------------------------------------------------------ *)
  let to_pure (tx : rtcenv -> 'a) (tc : tcenv) =
    let tc = ref tc in let x = tx tc in (!tc, x)

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
  let pf_get_pregoal_by_id id pf =
    FApi.get_pregoal_by_id id !pf

  let tc_get_pregoal_by_id id tc =
    FApi.get_pregoal_by_id id (!tc).tce_tcenv.tce_penv

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
  let tcenv = { tce_penv = pf.pr_env; tce_goal = None; tce_ctxt = []; } in
  let tcenv = { tce_tcenv = tcenv; tce_goals = []; } in
  FApi.tc_normalize tcenv

(* -------------------------------------------------------------------- *)
let tcenv1_of_proof (pf : proof) =
  FApi.tc_down (tcenv_of_proof pf)

(* -------------------------------------------------------------------- *)
let proof_of_tcenv (tc : tcenv) =
  let tc  = FApi.tc_uptop tc in
  let rg  = tc.tce_goals  in
  let fg  = tc.tce_tcenv.tce_goal |> omap (fun g -> g.g_uid) in

  { pr_env    = tc.tce_tcenv.tce_penv;
    pr_opened = List.ocons fg rg; }

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

  let recast_tc1 tc f =
    let penv = FApi.tc1_penv tc in
    let hyps = FApi.tc1_hyps tc in
      recast_pe penv (fun () -> f hyps)

  let recast_tc tc f =
    let penv = FApi.tc_penv tc in
    let hyps = FApi.tc_hyps tc in
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
  let tc1_process_form_opt tc pf oty =
    Exn.recast_tc1 tc (fun hyps -> process_form_opt hyps pf oty)

  let tc1_process_form tc pf ty =
    Exn.recast_tc1 tc (fun hyps -> process_form hyps pf ty)

  let tc1_process_formula tc pf =
    Exn.recast_tc1 tc (fun hyps -> process_formula hyps pf)

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
