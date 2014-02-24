(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcEnv

(* -------------------------------------------------------------------- *)
module ID : sig
  type id = private int

  val gen : unit -> int

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
module PT : sig
  val check : LDecl.hyps -> proofterm -> form
end = struct
  let check (_hyps : LDecl.hyps) (_pt : proofterm) =
    assert false
end

(* -------------------------------------------------------------------- *)
type position

type rwproofterm = {
  rpt_proof : proofterm;
  rtp_occrs : position list;
}

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
  g_uid   : ID.id;                      (* this goal ID *)
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

and location = {
  plc_parent : location option;
  plc_name   : string;
  plc_loc    : EcLocation.t;
}

(* -------------------------------------------------------------------- *)
module Api = struct
  type 'a forward  = 'a -> proofenv -> proofenv * handle
  type 'a backward = 'a -> tcenv -> tcenv
  type 'a mixward  = 'a -> tcenv -> tcenv * handle

  exception InvalidStateException of string

  let newgoal (tc : tcenv) ?(hyps:LDecl.hyps option) (goal : form) =
    assert false

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

  (* ------------------------------------------------------------------ *)
  let push_closed_to_tcenvx (hd : handle) (tcx : tcenv_ctxt) =
    { tcx with tcec_closed = ID.Set.add hd tcx.tcec_closed }

  (* ------------------------------------------------------------------ *)
  let close (tc : tcenv) (vx : validation) =
     check_tcenv_opened tc;

    let current = oget tc.tce_goal in

    let change g =
      if g.g_validation <> None || g.g_goal != current then
        raise (InvalidStateException "goal-map-inconsistent");
      { g with g_validation = Some vx }
    in

    (* Close current goal, set focused goal to None *)
    let tc = update_goal_map_on_tcenv change current.g_uid tc in
    let tc = { tc with tce_goal = None } in

    (* Maybe pop one opened goal from proof context *)
    let tc =
      let (sg, tcx) = pop_from_tcenvx tc.tce_subgoals in
        { tc with
            tce_goal     = sg |> omap (get_pregoal_by_id^~ tc.tce_proofenv);
            tce_subgoals = tcx; }
    in

    (* Register current goal has being closed *)
    { tc with tce_subgoals = push_closed_to_tcenvx current.g_uid tc.tce_subgoals }

  (* Tacticals *)
  type ontest    = int -> proofenv -> handle -> bool
  type direction = [ `Left | `Right ]

  let on (tt : 'a backward) (f : ontest) (x : 'a) (tc : tcenv) =
    assert false

  let first (tt : 'a backward) (i : int) (x : 'a) (tc : tcenv) =
    assert false

  let last (tt : 'a backward) (i : int) (x : 'a) (tc : tcenv) =
    assert false

  let rotate (d : direction) (i : int) (tc : tcenv) =
    assert false

  let seq (tt1 : 'a backward) (tt2 : 'a backward) (tc : tcenv) =
    assert false

  let lseq (tts : 'a backward list) (tc : tcenv) =
    assert false
end

(* -------------------------------------------------------------------- *)
module type IApi = sig
  type rprooftree
  type rtcenv
  type rtcenvs

  val freeze : rtcenv -> rtcenv
  val thaw   : rtcenv -> rtcenv
end
