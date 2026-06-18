(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcEnv
open EcTypes
open EcCoreGoal
open EcFol
open EcLowCircuits
open EcCircuits
open LDecl
open FApi

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

(* -------------------------------------------------------------------- *)
let form_list_from_iota (hyps : hyps) (f : form) : form list =
  match sform_of_form f with
  | SFop ((p, _), [n; m]) when EcPath.p_equal p EcCoreLib.CI_List.p_iota ->
    let n = int_of_form hyps n in
    let m = int_of_form hyps m in
    List.init (BI.to_int m) (fun i -> f_int BI.(add n (of_int i)))
  | _ -> raise (DestrError "iota")

let rec form_list_of_form (f : form) : form list =
  match sform_of_form f with
  | SFop ((p, _), []) when EcPath.p_equal p EcCoreLib.CI_List.p_empty -> []
  | SFop ((p, _), [h; t]) when EcPath.p_equal p EcCoreLib.CI_List.p_cons ->
    h :: form_list_of_form t
  | _ -> raise (DestrError "list")

(* -------------------------------------------------------------------- *)
let rec destr_conjunction (hyps : hyps) (f : form) : form list =
  let redmode = { (circ_red hyps) with zeta = false } in

  match sform_of_form (EcCallbyValue.norm_cbv redmode hyps f) with
  | SFand (_, (f1, f2)) ->
    destr_conjunction hyps f1 @ destr_conjunction hyps f2

  | SFop ((p, _), [pred; lst]) when EcPath.p_equal p EcCoreLib.CI_List.p_all -> begin
    match form_list_from_iota hyps lst with
    | fs -> List.map (fun farg -> f_app pred [farg] tbool) fs
    | exception DestrError _ -> [f]
  end

  | _ -> [f]

(* -------------------------------------------------------------------- *)
(* Should return a list of circuits corresponding to the atomic parts of the pre *)
(* 
  This means: 
  /\ p_i => [p_i]_i, 
  a = b  => [a.[i] = b.[i]]_i 
*)
(* Returns _open_ circuits *)
let process_pre ?(st : state option) (tc : tcenv1) (f : form) :
    state * circuit list =
  let hyps = FApi.tc1_hyps tc in

  (* Maybe move this to be a parameter and just supply it from outside *)
  let st =
    match st with
    | Some st -> st
    | None -> circuit_state_of_hyps hyps
  in

  (* Takes in a form of the form /\_i f_i 
     and returns a list of the conjunction terms [ f_i ]*)

  let fs = destr_conjunction hyps f in

  (* If f is of the form (a_ = a) (aka prog_var = log_var)
    then add it to the state, otherwise do nothing *)
  (* Processes explicit equations *)
  let process_equality (s : state) (f : form) : state =
    let f = EcCallbyValue.norm_cbv (circ_red hyps) hyps f in
    match sform_of_form f with
    | SFeq (a, b) -> begin
      match
        ( EcCallbyValue.norm_cbv (circ_red hyps) hyps a,
          EcCallbyValue.norm_cbv (circ_red hyps) hyps b )
      with
      | {f_node = Fpvar (PVloc pv, m); _}, fv
      | fv, {f_node = Fpvar (PVloc pv, m); _} ->
        update_state_pv s m pv (circuit_of_form st hyps fv)
      | _ -> s
    end
    | _ -> s
  in

  let st = List.fold_left process_equality st fs in

  (* If convertible to circuit then add to precondition conjunction.
     Use state from previous as well *)
  let process_form (f : form) : circuit list =
    match sform_of_form f with
    | SFeq (f1, f2) ->
      let c1 =
        circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f1)
      in
      let c2 =
        circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f2)
      in
      circuit_eqs c1 c2
    | _ -> begin
      try
        [
          circuit_of_form st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f);
        ]
      with _ -> []
    end
  in

  let cs =
    List.fold_left (fun acc f -> List.rev_append (process_form f) acc) [] fs
    |> List.rev
  in
  st, cs

(* -------------------------------------------------------------------- *)
let solve_post ~(st : state) ~(pres : circuit list) (hyps : hyps) (post : form)
    : bool =
  let env = toenv hyps in
  let lap = EcCircuits.stopwatch env in
  let posts = destr_conjunction hyps post in
  lap "Done with postcondition normalization (destr_conj)";
  let pres = List.map (state_close_circuit st) pres in

  posts |> List.to_seq
  |> Seq.concat_map (fun post ->
         match sform_of_form post with
         | SFeq (f1, f2) -> circuits_of_equality ~st ~hyps f1 f2 |> List.to_seq
         | _ ->
           Seq.return (circuit_of_form st hyps post |> state_close_circuit st))
  |> List.of_seq
  |> circuit_check_posts ~env ~pres

let t_bdep_solve (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let goal = FApi.tc1_goal tc in
  let env = FApi.tc1_env tc in
  match goal.f_node with
  | FhoareS hs -> begin
    try
      let lap = EcCircuits.stopwatch env in
      let st = create_state (EcEnv.gstate env) in
      let st = circuit_state_of_hyps ~st hyps in
      let st = circuit_state_of_memenv ~st env hs.hs_m in
      let st, cpres = process_pre ~st tc (hs_pr hs).inv in
      lap "Done with precondition processing";

      (* Get open state *)
      let st = state_of_prog hyps (fst hs.hs_m) ~st hs.hs_s.s_node in
      lap "Done with program circuit gen";

      if not (POE.is_empty (hs_po hs).hsi_inv) then
        tc_error !!tc "exception not supported";

      let res = solve_post ~st ~pres:cpres hyps (POE.lower (hs_po hs)).inv in
      EcCircuits.clear_translation_caches ();
      if res then FApi.close !@tc VBdep
      else tc_error (FApi.tc1_penv tc) "failed to verify postcondition"
    with CircError err ->
      tc_error (FApi.tc1_penv tc) "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv env))
        err
  end
  | FequivS es -> begin
    try
      let lap = EcCircuits.stopwatch env in

      let st = create_state (EcEnv.gstate env) in

      let st = circuit_state_of_hyps ~st hyps in
      let st = circuit_state_of_memenv ~st (FApi.tc1_env tc) es.es_ml in
      let st = circuit_state_of_memenv ~st (FApi.tc1_env tc) es.es_mr in

      let st, cpres = process_pre ~st tc (es_pr es).inv in
      lap "Done with precondition processing";

      (* Circuits from pvars are tagged by memory so we can just put everything in one state *)
      let st = state_of_prog hyps (fst es.es_ml) ~st es.es_sl.s_node in
      lap "Done with left program circuit gen";

      let st = state_of_prog hyps (fst es.es_mr) ~st es.es_sr.s_node in
      lap "Done with right program circuit gen";

      if solve_post ~st ~pres:cpres hyps (es_po es).inv then
        FApi.close !@tc VBdep
      else tc_error (FApi.tc1_penv tc) "failed to verify postcondition"
    with CircError err ->
      tc_error (FApi.tc1_penv tc) "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv env))
        err
  end
  | _ -> begin
    try
      let ctxt = tohyps hyps in
      assert (ctxt.h_tvar = []);
      let st = circuit_state_of_hyps hyps in
      let cgoal = circuit_of_form st hyps goal |> state_close_circuit st in
      if circ_valid cgoal then FApi.close !@tc VBdep
      else
        tc_error (FApi.tc1_penv tc)
          "Failed to solve goal through circuit reasoning@\n"
    with CircError err ->
      tc_error (FApi.tc1_penv tc) "circuit solve failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv env))
        err
  end

(* -------------------------------------------------------------------- *)
let t_bdep_simplify (tc : tcenv1) =
  let hyps = FApi.tc1_hyps tc in
  let goal = FApi.tc1_goal tc in
  let env = FApi.tc1_env tc in
  match goal.f_node with
  | FhoareS hs -> begin
    if not (POE.is_empty (hs_po hs).hsi_inv) then
      tc_error !!tc "exceptions not supported";
    try
      let m = fst hs.hs_m in
      let lap = EcCircuits.stopwatch env in
      let st = circuit_state_of_hyps hyps in
      let st = circuit_state_of_memenv ~st env hs.hs_m in
      let st, pres = process_pre ~st tc (hs_pr hs).inv in
      lap "Done with precondition processing";

      let st = EcCircuits.state_of_prog ~st hyps (fst hs.hs_m) hs.hs_s.s_node in
      let post =
        EcCallbyValue.norm_cbv (circ_red hyps) hyps (POE.lower (hs_po hs)).inv
      in

      lap "Done with first simplify";
      let f =
        EcCircuits.circ_simplify_form_bitstring_equality ~st ~pres hyps post
      in
      lap "Done with circuit simplify";
      let f = EcCallbyValue.norm_cbv EcReduction.full_red hyps f in
      lap "Done with second simplify";
      let new_goal =
        f_hoareS (snd hs.hs_m) {inv = (hs_pr hs).inv; m} hs.hs_s
          (POE.lift {inv = f; m})
      in

      FApi.mutate1 tc (fun _ -> VBdep) new_goal |> FApi.tcenv_of_tcenv1
    with CircError err ->
      tc_error (FApi.tc1_penv tc) "Circuit simplify failed with error: %a"
        (pp_circ_error EcPrinting.PPEnv.(ofenv env))
        err
  end
  | _ -> assert false


(* -------------------------------------------------------------------- *)
let t_extens (v : string option) (tt : backward) (tc : tcenv1) =
  (* Find goal shape 
       -> generate one goal for each value
       -> solve goal by applying the tactic
     *)
  let lap = EcCircuits.stopwatch (tc1_env tc) in

  let rec do_all (goals : form list) =
    match goals with
    | [] -> None
    | goal :: goals -> (
      let new_tc = mutate1 tc (fun _ -> VBdep) goal in
      match t_try_base tt new_tc with
      | `Failure e -> tc_error_exn (tc1_penv tc) e
      | `Success new_tc -> (
        match tc_opened new_tc with
        | [] ->
          do_all goals
        | hd :: _ -> Some (get_pregoal_by_id hd (tc_penv new_tc)).g_concl))
  in

  let subst_pv_stmt
      ?(redmode : EcReduction.reduction_info option)
      (hyps : LDecl.hyps)
      (mem : memory)
      (sb : EcPV.PVM.subst)
      (s : stmt) =
    let redmode = Option.default (circ_red hyps) redmode in
    let env = LDecl.toenv hyps in
    stmt
      (List.map
         (fun i ->
           match i.i_node with
           | Sasgn (lv, e) ->
             let f = ss_inv_of_expr mem e in
             let fi = EcPV.PVM.subst env sb f.inv in
             let fi = EcCallbyValue.norm_cbv redmode hyps fi in
             let e = expr_of_ss_inv {f with inv = fi} in
             EcCoreModules.i_asgn (lv, e)
           | _ -> raise CannotTranslate)
         s.s_node)
  in

  let goals =
    match sform_of_form (tc1_goal tc), v with
    | SFop ((p, [tp]), [fpred; flist]), None
      when EcPath.p_equal p EcCoreLib.CI_List.p_all && tp = tint ->
      begin
        match sform_of_form flist with
        | SFop ((p, []), [fstart; flen])
          when EcPath.p_equal p EcCoreLib.CI_List.p_iota ->
          let start =
            match sform_of_form fstart with
            | SFint i -> EcBigInt.to_int i
            | _ -> tc_error (tc1_penv tc) "Iota start should be constant"
          in

          let len =
            match sform_of_form flen with
            | SFint i -> EcBigInt.to_int i
            | _ -> tc_error (tc1_penv tc) "Iota length should be constant"
          in

          List.init len (fun i ->
              EcTypesafeFol.f_app (tc1_hyps tc) fpred
                [f_int EcBigInt.(of_int (i + start))])
        | _ -> tc_error (tc1_penv tc) "Unsupported List pattern"
      end
    | SFhoareS hs, Some v ->
      if not (POE.is_empty (hs_po hs).hsi_inv) then
        tc_error !!tc "exceptions not supported";

      let m, mt = hs.hs_m in
      let v =
        match EcMemory.lookup v mt with
        | Some (v, _, _) -> v
        | None ->
          tc_error (tc1_penv tc) "Failed to find var %s in memory %s" v
            (EcIdent.name m)
      in
      let size =
        match EcEnv.Circuit.lookup_bitstring_size (tc1_env tc) v.v_type with
        | Some size -> size
        | None ->
          tc_error (tc1_penv tc)
            "Failed to get size for type %a (is it finite and does it have a \
             binding to a bistring type (arrays unsupported)?)"
            EcPrinting.(pp_type PPEnv.(ofenv (tc1_env tc)))
            v.v_type
      in
      let tpath =
        match v.v_type.ty_node with
        | Tconstr (p, _) -> p
        | _ -> tc_error (tc1_penv tc) "Failed to destructure var type"
      in
      let of_int =
        match EcEnv.Circuit.reverse_type (tc1_env tc) tpath with
        | [] -> tc_error (tc1_penv tc) "No bindings found for type of var"
        | `Bitstring {ofint} :: _ -> ofint
        | _ -> tc_error (tc1_penv tc) "Only finite size bitstring supported"
      in
      let ngoals = 1 lsl size in
      List.init ngoals (fun i ->
          let subst =
            EcPV.PVM.(
              add (tc1_env tc) (PVloc v.v_name) (fst hs.hs_m)
                (EcTypesafeFol.f_op_app (tc1_env tc) of_int
                   [f_int BI.(of_int i)])
                empty)
          in
          let s = subst_pv_stmt (tc1_hyps tc) m subst hs.hs_s in
          let subst = EcPV.PVM.subst (tc1_env tc) subst in
          let pr = subst (hs_pr hs).inv in
          let po = subst (POE.lower (hs_po hs)).inv in
          f_hoareS mt {inv = pr; m} s (POE.lift {inv = po; m}))
    | _ -> tc_error (tc1_penv tc) "Wrong goal shape"
  in

  match do_all goals with
  | None ->
    lap "Extens";
    close (tcenv_of_tcenv1 tc) VBdep
  | Some gfail ->
    tc_error (tc1_penv tc) "Failed to close goal:@. %a"
      EcPrinting.(pp_form PPEnv.(ofenv (tc1_env tc)))
      gfail false
