(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcLocation
open EcUtils
open EcIdent
open EcTypes
open EcFol
open EcEnv

module L = EcLocation

(* -------------------------------------------------------------------- *)
exception InvalidGoalShape

(* -------------------------------------------------------------------- *)
type clearerror = [
  | `ClearInGoal of EcIdent.t list
  | `ClearDep    of EcIdent.t pair
]

exception ClearError of clearerror Lazy.t

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

let eq_handle (hd1 : handle) (hd2 : handle) =
  hd1 = hd2

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
let is_ptcut    = function PTCut    _ -> true | _ -> false
let is_pthandle = function PTHandle _ -> true | _ -> false
let is_ptlocal  = function PTLocal  _ -> true | _ -> false
let is_ptglobal = function PTGlobal _ -> true | _ -> false

(* -------------------------------------------------------------------- *)
let is_paformula = function PAFormula _ -> true | _ -> false
let is_pamemory  = function PAMemory  _ -> true | _ -> false
let is_pamodule  = function PAModule  _ -> true | _ -> false
let is_pasub     = function PASub     _ -> true | _ -> false

(* -------------------------------------------------------------------- *)
let paformula = fun x -> PAFormula x
let pamemory  = fun x -> PAMemory  x
let pamodule  = fun x -> PAModule  x

let paglobal p tys =
  PASub (Some { pt_head = PTGlobal (p, tys); pt_args = []; })

let palocal x =
  PASub (Some { pt_head = PTLocal x; pt_args = []; })

(* -------------------------------------------------------------------- *)
type rwproofterm = {
  rpt_proof : proofterm;
  rpt_occrs : EcMatching.ptnpos option;
  rpt_lc    : ident option;
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
| VLConv   of (handle * ident)       (* hypothesis conversion *)
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
type location = {
  plc_parent : location option;
  plc_name   : string option;
  plc_loc    : EcLocation.t;
}

type tcemsg =
| TCEUser : 'a * ('a -> string) -> tcemsg
| TCEExn  : exn -> tcemsg

type tcerror =  {
  tc_catchable : bool;
  tc_proofenv  : proofenv option;
  tc_location  : location option;
  tc_message   : tcemsg;
  tc_reloced   : (EcSymbols.symbol * bool) option;
}

let mk_location ?parent ?name loc =
  { plc_parent = parent; plc_name = name; plc_loc = loc; }

let mk_tcerror ?(catchable = true) ?penv ?loc msg =
  { tc_catchable = catchable;
    tc_proofenv  = penv;
    tc_location  = loc;
    tc_message   = (TCEUser (msg, Lazy.force));
    tc_reloced   = None; }

exception TcError of tcerror

(* -------------------------------------------------------------------- *)
let tc_error (penv : proofenv) ?(catchable = true) ?loc ?who fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
  let loc  = loc |> omap (fun loc -> mk_location loc) in
    ignore (who : string option);       (* FIXME: remove? *)
    Format.kfprintf
      (fun _ ->
         Format.pp_print_flush fbuf ();
         let error = lazy (Buffer.contents buf) in
         let error = mk_tcerror ~catchable ~penv ?loc error in
         raise (TcError error))
      fbuf fmt

(* -------------------------------------------------------------------- *)
let tc_error_exn (penv : proofenv) ?(catchable = true) ?loc ?who exn =
  ignore (who : string option);
  raise (TcError (
    { tc_catchable = catchable;
      tc_proofenv  = Some penv;
      tc_location  = loc |> omap (fun loc -> mk_location loc);
      tc_message   = (TCEExn exn);
      tc_reloced   = None; }))

(* -------------------------------------------------------------------- *)
let tacuerror ?(catchable = true) fmt =
  let buf  = Buffer.create 127 in
  let fbuf = Format.formatter_of_buffer buf in
    Format.kfprintf
      (fun _ ->
         Format.pp_print_flush fbuf ();
         let error = lazy (Buffer.contents buf) in
         raise (TcError (mk_tcerror ~catchable error)))
      fbuf fmt

(* -------------------------------------------------------------------- *)
let tacuerror_exn ?(catchable = true) exn =
  raise (TcError {
    tc_catchable = catchable;
    tc_proofenv  = None;
    tc_location  = None;
    tc_message   = (TCEExn exn);
    tc_reloced   = None; })

(* -------------------------------------------------------------------- *)
let tc_error_lazy (penv : proofenv) ?(catchable = true) ?loc ?who msg =
  let getmsg () =
    let buf  = Buffer.create 127 in
    let fbuf = Format.formatter_of_buffer buf in
      Format.fprintf fbuf "%t%!" msg;
      Buffer.contents buf
  in

  let loc = loc |> omap (fun loc -> mk_location loc) in

  ignore (who : string option);         (* FIXME: remove? *)
  raise (TcError (mk_tcerror ~catchable ~penv ?loc (lazy (getmsg ()))))

(* -------------------------------------------------------------------- *)
let tc_error_clear (pe : proofenv) ?catchable ?loc ?who err =
    tc_error_lazy pe ?catchable ?loc ?who (fun fmt ->
      let pp_id fmt id = Format.fprintf fmt "%s" (EcIdent.name id) in
      match Lazy.force err with
      | `ClearInGoal xs ->
          Format.fprintf fmt
            "cannot clear %a that is/are used in the conclusion"
            (EcPrinting.pp_list ",@ " pp_id) xs
      | `ClearDep (x, y) ->
          Format.fprintf fmt
            "cannot clear %a that is used in %a"
            pp_id x pp_id y)

(* -------------------------------------------------------------------- *)
type symkind = [`Lemma | `Operator | `Local]

let tc_lookup_error pe ?loc ?who kind qs =
  let string_of_kind kind =
    match kind with
    | `Lemma    -> "lemma"
    | `Operator -> "operator"
    | `Local    -> "local variable"
  in

  tc_error_lazy pe ~catchable:true ?loc ?who
    (fun fmt ->
      Format.fprintf fmt "unknown %s `%s'"
        (string_of_kind kind)
        (EcSymbols.string_of_qsymbol qs))

(* -------------------------------------------------------------------- *)
let reloc t f x =
  try  (f x)
  with TcError exn when is_none exn.tc_location ->
    let t = { plc_parent = None; plc_name = None; plc_loc = t } in
    raise (TcError { exn with tc_location = Some t })

(* -------------------------------------------------------------------- *)
module FApi = struct
  type forward   = proofenv -> proofenv * handle
  type backward  = tcenv1 -> tcenv
  type ibackward = int -> backward
  type tactical  = tcenv -> tcenv

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
  let get_main_pregoal (pe : proofenv) =
    get_pregoal_by_id pe.pr_main pe

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
  let as_tcenv1 (tc : tcenv) =
    if not (List.is_empty tc.tce_goals) then
      assert false;
    tc.tce_tcenv

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
  let tc1_handle (tc : tcenv1) =
    (tc1_current tc).g_uid

  (* ------------------------------------------------------------------ *)
  let tc1_flat ?target (tc : tcenv1) =
    let { g_hyps; g_concl } = tc1_current tc in
    match target with
    | None   -> (g_hyps, g_concl)
    | Some h -> (LDecl.local_hyps h g_hyps, LDecl.hyp_by_id h g_hyps)

  (* ------------------------------------------------------------------ *)
  let tc1_eflat ?target (tc : tcenv1) =
    let (hyps, concl) = tc1_flat ?target tc in
    (LDecl.toenv hyps, hyps, concl)

  (* ------------------------------------------------------------------ *)
  let tc1_hyps ?target (tc : tcenv1) = fst (tc1_flat ?target tc)

  (* ------------------------------------------------------------------ *)
  let tc1_penv (tc : tcenv1) = tc.tce_penv
  let tc1_goal (tc : tcenv1) = snd (tc1_flat tc)
  let tc1_env  (tc : tcenv1) = LDecl.toenv (tc1_hyps tc)

  (* ------------------------------------------------------------------ *)
  let tc_handle (tc : tcenv) = tc1_handle tc.tce_tcenv
  let tc_penv   (tc : tcenv) = tc1_penv   tc.tce_tcenv
  let tc_goal   (tc : tcenv) = tc1_goal   tc.tce_tcenv
  let tc_env    (tc : tcenv) = tc1_env    tc.tce_tcenv

  let tc_flat   ?target (tc : tcenv) = tc1_flat  ?target tc.tce_tcenv
  let tc_eflat  ?target (tc : tcenv) = tc1_eflat ?target tc.tce_tcenv
  let tc_hyps   ?target (tc : tcenv) = tc1_hyps  ?target tc.tce_tcenv

  (* ------------------------------------------------------------------ *)
  let tc_opened (tc : tcenv) =
    let goal = tc.tce_tcenv.tce_goal |> omap (fun g -> g.g_uid) in
    List.ocons goal tc.tce_goals

  (* ------------------------------------------------------------------ *)
  let tc_count (tc : tcenv) =
    List.length (tc_opened tc)

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
  let mutate (tc : tcenv) (vx : handle -> validation) ?hyps fp =
    let (tc, hd) = newgoal tc ?hyps fp in close tc (vx hd)

  (* ------------------------------------------------------------------ *)
  let mutate1 (tc : tcenv1) (vx : handle -> validation) ?hyps fp =
    let tc = mutate (tcenv_of_tcenv1 tc) vx ?hyps fp in
    assert (tc.tce_goals = []); tc.tce_tcenv

  (* ------------------------------------------------------------------ *)
  let xmutate (tc : tcenv) (vx : 'a) (fp : form list) =
    let (tc, hds) = List.map_fold (fun tc fp -> newgoal tc fp) tc fp in
    close tc (VExtern (vx, hds))

  (* ------------------------------------------------------------------ *)
  let xmutate1 (tc : tcenv1) (vx : 'a) (fp : form list) =
    xmutate (tcenv_of_tcenv1 tc) vx fp

  (* ------------------------------------------------------------------ *)
  let xmutate_hyps (tc : tcenv) (vx : 'a) subgoals =
    let (tc, hds) =
      List.map_fold
        (fun tc (hyps, fp) -> newgoal tc ~hyps fp)
        tc subgoals
    in
      close tc (VExtern (vx, hds))

  (* ------------------------------------------------------------------ *)
  let xmutate1_hyps (tc : tcenv1) (vx : 'a) subgoals =
    xmutate_hyps (tcenv_of_tcenv1 tc) vx subgoals

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
  let t_low0 (_ : string) tt tc         = tt tc
  let t_low1 (_ : string) tt x tc       = tt x tc
  let t_low2 (_ : string) tt x y tc     = tt x y tc
  let t_low3 (_ : string) tt x y z tc   = tt x y z tc
  let t_low4 (_ : string) tt x y z w tc = tt x y z w tc

  (* ------------------------------------------------------------------ *)
  let tc_done (tc : tcenv) =
    EcUtils.is_none (tc_normalize tc).tce_tcenv.tce_goal

  (* ------------------------------------------------------------------ *)
  (* Tacticals *)
  type direction = [ `Left | `Right ]
  type tfocus    = (int -> bool)

  (* ------------------------------------------------------------------ *)
  let t_focus (tt : backward) (tc : tcenv) =
    tc_up (tt (tc_down tc))

  (* ------------------------------------------------------------------ *)
  let on_sub1i_goals (tt : int -> backward) (hds : handle list) (pe : proofenv) =
    let do1 i pe hd =
      let tc = tt i (tcenv1_of_penv hd pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      (tc_penv tc, tc_opened tc) in
    List.mapi_fold do1 pe hds

  (* ------------------------------------------------------------------ *)
  let on_sub1_goals (tt : backward) (hds : handle list) (pe : proofenv) =
    on_sub1i_goals (fun (_ : int) -> tt) hds pe

  (* ------------------------------------------------------------------ *)
  let on_sub1i_map_goals
    (tt : int -> tcenv1 -> 'a * tcenv) (hds : handle list) (pe : proofenv)
  =
    let do1 i pe hd =
      let data, tc = tt i (tcenv1_of_penv hd pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      (tc_penv tc, (tc_opened tc, data)) in
    List.mapi_fold do1 pe hds

  (* ------------------------------------------------------------------ *)
  let on_sub1_map_goals
    (tt : tcenv1 -> 'a * tcenv) (hds : handle list) (pe : proofenv)
  = on_sub1i_map_goals (fun (_ : int) -> tt) hds pe

  (* ------------------------------------------------------------------ *)
  let on_sub_goals (tt : backward list) (hds : handle list) (pe : proofenv) =
    let do1 pe tt hd =
      let tc = tt (tcenv1_of_penv hd pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      (tc_penv tc, tc_opened tc) in
    List.map_fold2 do1 pe tt hds

  (* ------------------------------------------------------------------ *)
  let t_onalli (tt : ibackward) (tc : tcenv) =
    let pe      = tc.tce_tcenv.tce_penv in
    let pe, ln  = on_sub1i_goals tt (tc_opened tc) pe in
    let ln      = List.flatten ln in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt ln pe

  (* ------------------------------------------------------------------ *)
  let t_onall (tt : backward) (tc : tcenv) =
    t_onalli (fun (_ : int) -> tt) tc

  (* ------------------------------------------------------------------ *)
  let t_map (tt : tcenv1 -> 'a * tcenv) (tc : tcenv) =
    let pe      = tc.tce_tcenv.tce_penv in
    let pe, ln  = on_sub1_map_goals tt (tc_opened tc) pe in
    let ln, dt  = fst_map List.flatten (List.split ln) in
    (dt, tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt ln pe)
    
  (* ------------------------------------------------------------------ *)
  let t_firsts (tt : backward) (i : int) (tc : tcenv) =
    if i < 0 then invalid_arg "EcCoreGoal.firsts";
    let (ln1, ln2) = List.takedrop i (tc_opened tc) in
    let pe, ln1    = on_sub1_goals tt ln1 tc.tce_tcenv.tce_penv in
    let handles    = (List.flatten (ln1 @ [ln2])) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  (* ------------------------------------------------------------------ *)
  let t_lasts (tt : backward) (i : int) (tc : tcenv) =
    if i < 0 then invalid_arg "EcCoreGoal.lasts";
    let handles    = tc_opened tc in
    let nhandles   = List.length handles in
    let (ln1, ln2) = List.takedrop (max 0 (nhandles-i)) handles in
    let pe, ln2    = on_sub1_goals tt ln2 tc.tce_tcenv.tce_penv in
    let handles    = (List.flatten (ln1 :: ln2)) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  (* ------------------------------------------------------------------ *)
  let t_first (tt : backward) (tc : tcenv) = t_firsts tt 1 tc
  let t_last  (tt : backward) (tc : tcenv) = t_lasts  tt 1 tc

  (* ------------------------------------------------------------------ *)
  let t_subfirsts (tt : backward list) (tc : tcenv) =
    let (ln1, ln2) = List.takedrop (List.length tt) (tc_opened tc) in
    let pe, ln1    = on_sub_goals tt ln1 tc.tce_tcenv.tce_penv in
    let handles    = (List.flatten (ln1 @ [ln2])) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  (* ------------------------------------------------------------------ *)
  let t_sublasts (tt : backward list) (tc : tcenv) =
    let handles    = tc_opened tc in
    let nhandles   = List.length handles in
    let (ln1, ln2) = List.takedrop (max 0 (nhandles-(List.length tt))) handles in
    let pe, ln2    = on_sub_goals tt ln2 tc.tce_tcenv.tce_penv in
    let handles    = (List.flatten (ln1 :: ln2)) in
    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt handles pe

  (* ------------------------------------------------------------------ *)
  let t_onfsub (tx : int -> backward option) (tc : tcenv) =
    let do1 pe i hd =
      let tt = odfl tcenv_of_tcenv1 (tx i) in
      let tc = tt (tcenv1_of_penv hd !pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      pe := (tc_penv tc); tc_opened tc
    in

    let pe = ref (tc_penv tc) in
    let ln = List.mapi (do1 pe) (tc_opened tc) in

    tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt (List.flatten ln) !pe

  (* ------------------------------------------------------------------ *)
  let t_onfsub_map (tx : int -> tcenv1 -> 'a * tcenv) (tc : tcenv) =
    let do1 pe i hd =
      let data, tc = tx i (tcenv1_of_penv hd !pe) in
      assert (tc.tce_tcenv.tce_ctxt = []);
      pe := (tc_penv tc); (tc_opened tc, data)
    in

    let pe = ref (tc_penv tc) in
    let ln, data = List.split (List.mapi (do1 pe) (tc_opened tc)) in

    (data, tcenv_of_penv ~ctxt:tc.tce_tcenv.tce_ctxt (List.flatten ln) !pe)

  (* ------------------------------------------------------------------ *)
  let t_sub (ts : backward list) (tc : tcenv) =
    let ts = Array.of_list ts in
    if Array.length ts <> tc_count tc then
      raise InvalidGoalShape;
    t_onfsub (fun i -> Some ts.(i)) tc

  (* -------------------------------------------------------------------- *)
  let t_submap (ts : (tcenv1 -> 'a * tcenv) list) (tc : tcenv) =
    let ts = Array.of_list ts in
    if Array.length ts <> tc_count tc then
      raise InvalidGoalShape;
    t_onfsub_map (fun i -> ts.(i)) tc

  (* ------------------------------------------------------------------ *)
  let t_onselecti (test : tfocus) ?ttout (tt : ibackward) (tc : tcenv) =
    let ttout i = ttout |> omap (fun ttout -> ttout i) in

    if   tc_count tc > 0
    then t_onfsub (fun i -> if test i then Some (tt i) else ttout i) tc
    else tc

  (* ------------------------------------------------------------------ *)
  let t_onselect (test : tfocus) ?ttout (tt : backward) (tc : tcenv) =
    t_onselecti test
      ?ttout:(ttout |> omap (fun ttout (_ : int) -> ttout))
      (fun (_ : int) -> tt)
      tc

  (* ------------------------------------------------------------------ *)
  let t_on1 idx ?ttout tt (tc : tcenv) =
    t_onselect ((=) idx) ?ttout tt tc

  (* ------------------------------------------------------------------ *)
  let t_rotate (d : direction) (i : int) (tc : tcenv) =
    match tc.tce_tcenv.tce_goal with
    | None    -> tc
    | Some _g ->
        match List.rotate d (max i 0) (tc_opened tc) with
        | 0, _ -> tc
        | _, s ->
            let tcenv = { tc.tce_tcenv with tce_goal = None; } in
            let tc    = { tc with tce_goals = s; tce_tcenv = tcenv; } in
            tc_normalize tc

  (* ------------------------------------------------------------------ *)
  let t_swap_goals (g:int) (delta:int) (tc:tcenv) =
    if delta = 0 || tc.tce_tcenv.tce_goal = None then tc
    else
      let s = 
        let rgs1, g, gs2 =
          try  List.pivot_at g (tc_opened tc)
          with Invalid_argument _ -> raise InvalidGoalShape
        in
        if delta < 0 then
          let len = List.length rgs1 in
          let rgs2, rgs1 = List.takedrop (min (-delta) len) rgs1 in
          List.rev_append rgs1 (g :: List.rev_append rgs2 gs2)
        else
          let len = List.length gs2 in
          let gs1, gs2 = List.takedrop (min delta len) gs2 in
          List.rev_append rgs1 (gs1 @ g :: gs2) in
      let tcenv = { tc.tce_tcenv with tce_goal = None; } in
      let tc    = { tc with tce_goals = s; tce_tcenv = tcenv; } in
      tc_normalize tc

  (* ------------------------------------------------------------------ *)
  let t_seq (tt1 : backward) (tt2 : backward) (tc : tcenv1) =
    t_onall tt2 (tt1 tc)

  (* ------------------------------------------------------------------ *)
  let t_seqs (tts : backward list) (tc : tcenv1) =
    List.fold_left (fun tc tt -> t_onall tt tc) (tcenv_of_tcenv1 tc) tts

  (* ------------------------------------------------------------------ *)
  let t_seqsub (tt : backward) (ts : backward list) (tc : tcenv1) =
    t_sub ts (tt tc)

  (* ------------------------------------------------------------------ *)
  let t_on1seq idx tt1 ?ttout tt2 tc =
    (t_on1 idx ?ttout tt2) (tt1 tc)

  (* ------------------------------------------------------------------ *)
  let t_internal ?(info : string option) (tt : backward) (tc : tcenv1) =
    ignore info; tt tc

  (* ------------------------------------------------------------------ *)
  let t_try_base tt tc =
    let rec is_user_error = function
      | EcTyping.TyError  _ -> true
      | InvalidGoalShape    -> true
      | ClearError _        -> true
      | LocError (_, e)     -> is_user_error e
      | TcError tc          -> tc.tc_catchable
      | _ -> false
    in

    try `Success (tt tc)
    with e when is_user_error e -> `Failure e

  let t_try (tt : backward) (tc : tcenv1) =
    match t_try_base tt tc with
    | `Failure _  -> tcenv_of_tcenv1 tc
    | `Success tc -> tc

  (* ------------------------------------------------------------------ *)
  let t_switch ?(on = `Focus) tt ~ifok ~iffail tc =
    match on, t_try_base tt tc with
    | _     , `Failure _  -> iffail tc
    | `All  , `Success tc -> t_onall ifok tc
    | `Focus, `Success tc -> t_focus ifok tc

  (* ------------------------------------------------------------------ *)
  let t_do_r ?focus b omax t tc =
    let max = max (odfl max_int omax) 0 in

    let rec doit i tc =
      let hd = tc1_handle tc in
      let r  = if i < max then Some (t_try_base t tc) else None in

      match r with
      | None -> tcenv_of_tcenv1 tc

      | Some (`Failure e) ->
          let fail =
            match b, omax with
            | `Maybe, _      -> false
            | `All  , None   -> i < 1
            | `All  , Some m -> i < m
          in
            if fail then raise e else tcenv_of_tcenv1 tc

      | Some (`Success tc) ->
          match tc_opened tc with
          | [] -> tc
          | [hd'] when eq_handle hd hd' -> tc
          | _ -> doit_focus (i+1) tc

    and doit_focus i tc =
      match focus with
      | None   -> t_onall (doit i) tc
      | Some f -> t_on1 f (doit i) tc

    in doit_focus 0 tc

  (* ------------------------------------------------------------------ *)
  let t_do b omax t tc =
    t_do_r b omax t (tcenv_of_tcenv1 tc)

  (* ------------------------------------------------------------------ *)
  let t_repeat tt tc =
    t_do `Maybe None tt tc

  (* ------------------------------------------------------------------ *)
  let t_or (tt1 : backward) (tt2 : backward) (tc : tcenv1) =
    match t_try_base tt1 tc with
    | `Success tc -> tc
    | `Failure _  -> tt2 tc

  (* ------------------------------------------------------------------ *)
  let t_ors_pmap (totc : 'a -> backward option) (xs : 'a list) (tc : tcenv1) =
    let rec doit (failure : exn option) xs =
      match xs, failure with
      | [], None   -> tcenv_of_tcenv1 tc
      | [], Some e -> raise e

      | x :: xs, _ ->
          match totc x with
          | None    -> doit failure xs
          | Some tt ->
              match t_try_base tt tc with
              | `Success tc -> tc
              | `Failure e  -> doit (Some e) xs

    in doit None xs

  (* ------------------------------------------------------------------ *)
  let t_ors_map (totc : 'a -> backward) (xs : 'a list) (tc : tcenv1) =
    t_ors_pmap (some |- totc) xs tc

  (* ------------------------------------------------------------------ *)
  let rec t_ors (tts : backward list) (tc : tcenv1) =
    t_ors_pmap (fun x -> Some x) tts tc
end

(* -------------------------------------------------------------------- *)
let (!!) = FApi.tc1_penv
let (!$) = FApi.tc_penv
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
  let tc_goal  (tc : rtcenv) = FApi.tc_goal  !tc
  let tc_env   (tc : rtcenv) = FApi.tc_env   !tc

  let tc_flat  ?target (tc : rtcenv) = FApi.tc_flat  ?target !tc
  let tc_eflat ?target (tc : rtcenv) = FApi.tc_eflat ?target !tc
  let tc_hyps  ?target (tc : rtcenv) = FApi.tc_hyps  ?target !tc
end

type rproofenv = RApi.rproofenv
type rtcenv    = RApi.rtcenv

(* -------------------------------------------------------------------- *)
let tcenv_of_proof (pf : proof) =
  let tcenv = { tce_penv = pf.pr_env; tce_goal = None; tce_ctxt = []; } in
  let tcenv = { tce_tcenv = tcenv; tce_goals = pf.pr_opened; } in
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
let proofenv_of_proof (pf : proof) =
  pf.pr_env

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
let all_hd_opened (pf : proof) =
  pf.pr_opened

(* -------------------------------------------------------------------- *)
let all_opened (pf : proof) =
  pf.pr_opened |> List.map ((^~) FApi.get_pregoal_by_id pf.pr_env)

(* -------------------------------------------------------------------- *)
let closed (pf : proof) = List.is_empty pf.pr_opened

(* -------------------------------------------------------------------- *)
module Exn = struct
  let recast pe _hyps f x =
    try  f x
    with (EcTyping.RestrictionError _) as e ->
      tc_error_exn pe e

  let recast_pe pe hyps f =
    recast pe hyps f ()

  let recast_tc1 tc f =
    let penv = FApi.tc1_penv tc in
    let hyps = FApi.tc1_hyps tc in
    recast_pe penv hyps (fun () -> f hyps)

  let recast_tc tc f =
    let penv = FApi.tc_penv tc in
    let hyps = FApi.tc_hyps tc in
    recast_pe penv hyps (fun () -> f hyps)
end
