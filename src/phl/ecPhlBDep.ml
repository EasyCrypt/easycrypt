(* -------------------------------------------------------------------- *)
open EcUtils
open EcIdent
open EcSymbols
open EcLocation
open EcParsetree
open EcAst
open EcEnv
open EcTypes
open EcCoreGoal
open EcFol
open EcLowCircuits
open EcCircuits
open LDecl

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

(* -------------------------------------------------------------------- *)
exception BDepError of string Lazy.t
exception BDepUninitializedInputs
exception BadTypeForConstructor
exception TyLookupError
exception BDepVerifyFail

(* TODO: Refactor error printing and checking? Lots of duplicated code *)

let int_of_form = EcCircuits.int_of_form

let time (env: env) (t: float) (msg: string) : float =
  let new_t = Unix.gettimeofday () in
  EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. t);
  new_t

(* 
   f => arr_t.init (fun i => f.(i + offset)) 
  Assumes f has an array type binding
  Assumes f has enough positions so that 
  arr_t.size + offset < size f (as array)
*)
let array_init_from_form (env: env) (f: form) ((arr_t, offset): qsymbol * BI.zint) : form =
  let ppe = EcPrinting.PPEnv.ofenv env in
  let tpath = match EcEnv.Ty.lookup_opt arr_t env with
  | None -> raise TyLookupError
  | Some (path, decl) when List.length decl.tyd_params = 1 ->
    path
  | Some ((_path, decl) as tdecl) ->
    raise BadTypeForConstructor
  in
  let get = match EcEnv.Circuit.lookup_array env f.f_ty with
  | Some { get } -> get
  | None -> raise (MissingTyBinding f.f_ty)
  in
  let init = EcEnv.Op.lookup_path (fst (tpath |> EcPath.toqsymbol), "init") env in
  let idx = create "i" in
  let f = f_lambda [(idx, GTty tint)] 
    (EcTypesafeFol.f_app_safe env get [f; f_int_add (f_local idx tint) (f_int offset)]) 
  in EcTypesafeFol.f_app_safe env init [f]

(* FIXME: move? V *)
let form_list_from_iota (hyps: hyps) (f: form) : form list =
  match f.f_node with
  | Fapp ({f_node = Fop(p, _)}, [n; m]) when p = EcCoreLib.CI_List.p_iota ->
    let n = int_of_form hyps n in
    let m = int_of_form hyps m in
    List.init (BI.to_int m) (fun i -> f_int (BI.(add n (of_int i))))
  | _ -> 
    raise (DestrError "iota") 

let rec form_list_of_form ?(ppenv: EcPrinting.PPEnv.t option) (f: form) : form list =
  match destr_op_app f with
  | (pc, _), [h; {f_node = Fop(p, _)}] when 
    pc = EcCoreLib.CI_List.p_cons && 
    p = EcCoreLib.CI_List.p_empty ->
    [h]
  | (pc, _), [h; t] when
    pc = EcCoreLib.CI_List.p_cons ->
    h::(form_list_of_form t)
  | _ -> 
      raise (DestrError "list")

(* FIXME: move? A *)

let rec destr_conj (hyps: hyps) (f: form) : form list = 
  let redmode = {(circ_red hyps) with zeta = false} in
  let f = (EcCallbyValue.norm_cbv redmode hyps f) in
  match f.f_node with
  | Fapp ({f_node = Fop (p, _)}, fs) -> begin match (EcFol.op_kind p, fs) with
    | Some (`And _), _ -> List.flatten @@ List.map (destr_conj hyps) fs
    | (None, [f;fs]) when p = EcCoreLib.CI_List.p_all -> 
      let fs = form_list_from_iota hyps fs in
      List.map (fun farg -> f_app f (farg::[]) tbool) fs
    | _ -> f::[]
  end
  | _ -> f::[]


(* Should return a list of circuits corresponding to the atomic parts of the pre *)
(* 
  This means: 
  /\ p_i => [p_i]_i, 
  a = b  => [a.[i] = b.[i]]_i 
*)
(* Returns _open_ circuits *)
let process_pre ?(st : state option) (tc: tcenv1) (f: form) : state * circuit list = 
  let debug = false in
  let env = FApi.tc1_env tc in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let hyps = FApi.tc1_hyps tc in (* FIXME: should target be specified here? *)

  (* Maybe move this to be a parameter and just supply it from outside *)
  let st = match st with
  | Some st -> st 
  | None -> circuit_state_of_hyps hyps 
  in

  (* Takes in a form of the form /\_i f_i 
     and returns a list of the conjunction terms [ f_i ]*)
  let destr_conj = destr_conj hyps in

  let fs = destr_conj f in

  if debug then Format.eprintf "Destructured conj, obtained:@.%a@."
    (EcPrinting.pp_list ";@\n" EcPrinting.(pp_form PPEnv.(ofenv env))) fs;

  (* If f is of the form (a_ = a) (aka prog_var = log_var) 
    then add it to the state, otherwise do nothing *)
  (* FIXME: are all the simplifications necessary ? *)
  let rec process_equality (s: state) (f: form) : state = 
    let f = (EcCallbyValue.norm_cbv (circ_red hyps) hyps f) in
    match f.f_node with
    | Fapp ({f_node = Fop (p, _);_}, [a; b]) -> begin match EcFol.op_kind p, (EcCallbyValue.norm_cbv (circ_red hyps) hyps a), (EcCallbyValue.norm_cbv (circ_red hyps) hyps b) with
      | Some `Eq, {f_node = Fpvar (PVloc pv, m); _}, fv
      | Some `Eq, fv, {f_node = Fpvar (PVloc pv, m); _} -> 
        if debug then Format.eprintf "Adding equality to known information for translation: %a@." EcPrinting.(pp_form PPEnv.(ofenv env)) f;
        update_state_pv s m pv (circuit_of_form ~st hyps fv)
      | _ -> s
    end 
    | _ -> s
  in

  let st = List.fold_left process_equality st fs in

  (* If convertible to circuit then add to precondition conjunction.
     Use state from previous as well *)
  let rec process_form (f: form) : circuit list = 
    match f.f_node with
    | Fapp ({f_node = Fop (p, _);_}, [f1; f2]) when EcFol.op_kind p = Some `Eq -> 
      let c1 = circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f1) in
      let c2 = circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f2) in
      circuit_eqs c1 c2
    | _ -> 
      begin
      if debug then
      Format.eprintf "Processing form: %a@.Simplified version: %a@."
        EcPrinting.(pp_form ppe) f
        EcPrinting.(pp_form ppe) (EcCallbyValue.norm_cbv (circ_red hyps) hyps f);
      try (circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f))::[] with
      e -> begin 
        if debug then Format.eprintf "Encountered exception when converting part of the pre to circuit: %s@." (Printexc.to_string e);
        [] end
      end
  in

  let cs = List.fold_left (fun acc f -> List.rev_append (process_form f) acc) [] fs |> List.rev in
(*
  if debug then Format.eprintf "Translated as much as possible from pre to circuits, got:@.%a@\n"
    (EcPrinting.pp_list "@\n@\n" pp_circuit) cs;
*)

  if debug then Format.eprintf  "In the context of the following bindings in the environment:@\n%a@\n"
  (EcPrinting.pp_list "@\n@\n" (fun fmt cinp -> Format.eprintf "%a@." pp_cinp cinp)) (state_lambdas st);
  st, cs

let solve_post ~(st: state) ~(pres: circuit list) (hyps: hyps) (post: form) : bool =
  let destr_conj = destr_conj hyps in
  let posts = destr_conj post in

  List.for_all (fun post ->
  if debug then Format.eprintf "Solving post: %a@." 
  EcPrinting.(pp_form PPEnv.(ofenv (toenv hyps))) post;
  match post.f_node with
  | Fapp ({f_node= Fop(p, _); _}, [f1; f2]) -> 
    begin match EcFol.op_kind p with
    | Some `Eq -> 
      circuit_simplify_equality ~st ~hyps ~pres f1 f2 
    | _ -> circuit_of_form ~st hyps post |> state_close_circuit st |> circ_taut
  end
  | _ -> circuit_of_form ~st hyps post |> state_close_circuit st |> circ_taut
  ) posts

(* TODO: Figure out how to not repeat computations here? *) 
let t_bdep_solve
  (tc : tcenv1) =
  let time (env: env) (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in

  begin 
    let hyps = (FApi.tc1_hyps tc) in
    let goal = (FApi.tc1_goal tc) in
    match goal.f_node with 
    | FhoareS {hs_m; hs_pr; hs_po; hs_s} -> begin try
      let tm = Unix.gettimeofday () in
      let st, cpres = process_pre tc hs_pr in
      let tm = time (toenv hyps) tm "Done with precondition processing" in

      let st = state_of_prog hyps (fst hs_m) ~st hs_s.s_node in
      let _tm = time (toenv hyps) tm "Done with program circuit gen" in
      let res = solve_post ~st ~pres:cpres hyps hs_po in
      EcCircuits.clear_translation_caches ();
      if res then 
        FApi.close (!@ tc) VBdep 
      else
        raise BDepVerifyFail (* FIXME: this is tactic failure, maybe should be done differently? *)
      with 
      (* FIXME: not catching anything, redo *)
      | BDepError le
      | CircError le ->
        tc_error (FApi.tc1_penv tc) "%s" (Lazy.force le)
    end
    | FequivS { es_ml; es_mr; es_pr; es_sl; es_sr; es_po } -> 
    begin 
      try (
        let tm = Unix.gettimeofday () in
        (* FIXME: rework this *)
        let st = circuit_state_of_memenv ~st:empty_state (FApi.tc1_env tc) es_ml in
        let st = circuit_state_of_memenv ~st (FApi.tc1_env tc) es_mr in
(*         let st = circuit_state_of_hyps ~st (FApi.tc1_hyps tc) in *)
        let st, cpres = process_pre ~st tc es_pr in
        let tm = time (toenv hyps) tm "Done with precondition processing" in

        (* Circuits from pvars are tagged by memory so we can just put everything in one state *)
        let st = state_of_prog ~me:es_ml hyps (fst es_ml) ~st es_sl.s_node in
        let tm = time (toenv hyps) tm "Done with left program circuit gen" in
        let st = state_of_prog ~me:es_mr hyps (fst es_mr) ~st es_sr.s_node in
        let _tm = time (toenv hyps) tm "Done with right program circuit gen" in

        (if solve_post ~st ~pres:cpres hyps es_po
        then FApi.close (!@ tc) VBdep else
        raise BDepVerifyFail)
      )
      with 
      (* FIXME: not catching anything, redo *)
      | BDepError le
      | CircError le ->
        tc_error (FApi.tc1_penv tc) "%s" (Lazy.force le)
    end
    | _ -> 
    let ctxt = tohyps hyps in
    assert (ctxt.h_tvar = []);
    let st = circuit_state_of_hyps hyps in
    let cgoal = (circuit_of_form ~st hyps goal |> state_close_circuit st) in
    if debug then Format.eprintf "goal: %a@." pp_flatcirc (fst cgoal).reg;
    if circ_taut cgoal then
    FApi.close (!@ tc) VBdep
    else 
    tc_error (FApi.tc1_penv tc) "Failed to solve goal through circuit reasoning@\n"  
  end

let t_bdep_simplify (tc: tcenv1) =
  let time (env: env) (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. t);
    Format.eprintf "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in
  let hyps = (FApi.tc1_hyps tc) in
  let goal = (FApi.tc1_goal tc) in
  let env  = (FApi.tc1_env  tc) in
  match goal.f_node with 
  | FhoareS {hs_m=(m, me) as hs_m; hs_pr; hs_po; hs_s} -> 
(*     begin try *)
      let tm = Unix.gettimeofday () in
      let st = circuit_state_of_hyps ~use_mem:true hyps in
      let st = circuit_state_of_memenv ~st env hs_m in
      let st, pres = process_pre ~st tc hs_pr in
      let tm = time env tm "Done with precondition processing" in


      let st = try
        EcCircuits.state_of_prog ~st hyps (fst hs_m) hs_s.s_node 
      (* FIXME: not catching anything, redo *)
      with CircError (lazy err) ->
        tc_error (FApi.tc1_penv tc) "CircError: @.%s" err
      in
      let post = EcCallbyValue.norm_cbv (circ_red hyps) hyps hs_po in
  (*
      if debug then Format.eprintf "[W] Post after simplify (before circuit pass):@. %a@."
        EcPrinting.(pp_form PPEnv.(ofenv env)) post;
  *)
      let tm = time env tm "Done with first simplify" in
      let f = EcCircuits.circ_simplify_form_bitstring_equality ~st ~pres hyps post in
      let tm = time env tm "Done with circuit simplify" in
      let f = EcCallbyValue.norm_cbv (EcReduction.full_red) hyps f in
      let _tm = time env tm "Done with second simplify" in
      let new_goal = f_hoareS (snd hs_m) {inv=hs_pr; m} hs_s {inv=f; m} in
  (*
      if debug then Format.eprintf "[W] Goal after simplify:@. %a@."
        EcPrinting.(pp_form PPEnv.(ofenv env)) new_goal;
  *)
      
      FApi.mutate1 tc (fun _ -> VBdep) new_goal |> FApi.tcenv_of_tcenv1
(*
    with CircError err ->
      tc_error (FApi.tc1_penv tc) "CircError: %s@." (Lazy.force err)
    end
*)
  | _ -> assert false (* FIXME : TODO *)

(* ================ EXTENS TACTIC  ==================== *)
(* FIXME: Maybe move later? *)
open FApi
let t_extens (v: string option) (tt : backward) (tc : tcenv1) =
    (* Find goal shape 
       -> generate one goal for each value
       -> solve goal by applying the tactic
     *)

    let open EcAst in

    let tm = Unix.gettimeofday () in

    let solved = ref 0 in

    let rec do_all (goals: form list) =
      match goals with
      | [] -> None
      | goal::goals -> 
        let new_tc = mutate1 tc (fun _ -> VBdep) goal in
        match (t_try_base tt new_tc) with
        | `Failure e -> 
            tc_error_exn (tc1_penv tc) e
        | `Success new_tc ->
          match tc_opened new_tc with
          | [] -> 
              incr solved;
              (* EcEnv.notify ~immediate:true (tc1_env tc) `Warning "Solved goal %d@." !solved; *)
              do_all goals
          | hd::_ -> 
            Some (get_pregoal_by_id hd (tc_penv new_tc)).g_concl
    in

    let subst_pv_stmt ?(redmode: EcReduction.reduction_info option) (hyps: LDecl.hyps) (mem: memory) (sb: EcPV.PVM.subst) (s: stmt) =
      let redmode = Option.default (circ_red hyps) redmode in 
      let env = LDecl.toenv hyps in
      stmt (List.map (fun i ->
        match i.i_node with
        | Sasgn (lv, e) ->
        let f = (ss_inv_of_expr mem e) in
        let fi = EcPV.PVM.subst env sb f.inv in
        let fi = EcCallbyValue.norm_cbv redmode hyps fi in
        let e = try expr_of_ss_inv {f with inv=fi}
          with CannotTranslate ->
            Format.eprintf "Failed on form : %a@."
            EcPrinting.(pp_form PPEnv.(ofenv env)) fi;
            raise CannotTranslate
        in
        EcCoreModules.i_asgn (lv, e)
        | _ -> raise (CannotTranslate) (* FIXME: Errors *)

      ) s.s_node)
    in

    let goals = match (tc1_goal tc).f_node, v with 
    | Fapp ({f_node = Fop (p, [tint]); _}, [fpred; flist]), None when p = EcCoreLib.CI_List.p_all ->
        Format.eprintf "[W] Found list all@.";
        begin match flist.f_node with
        | Fapp ({f_node = Fop (p, []); _}, [fstart; flen]) when p = EcCoreLib.CI_List.p_iota ->
          let start = match fstart.f_node with
          | Fint i -> EcBigInt.to_int i
          | _ -> tc_error (tc1_penv tc) "Iota start should be constant"
          in

          let len = match flen.f_node with
          | Fint i -> EcBigInt.to_int i
          | _ -> tc_error (tc1_penv tc) "Iota length should be constant"
          in

          let goals = List.init len (fun i -> 
            EcTypesafeFol.fapply_safe (tc1_hyps tc) fpred [f_int EcBigInt.(of_int (i + start))]
          ) in

          Format.eprintf "[w] Got iota => [%d, %d)@.Goals: %a@." start len 
          EcPrinting.(pp_list " | " (pp_form PPEnv.(ofenv (tc1_env tc)))) goals;
          goals

          | _ -> tc_error (tc1_penv tc) "Unsupported List pattern"
        end
    | FhoareS ({ hs_m=(m, mt); hs_s; hs_pr; hs_po }), Some v -> 
      let v = match EcMemory.lookup v mt with
      | Some (v, _, _) -> v 
      | None -> tc_error (tc1_penv tc) "Failed to find var %s in memory %s" v (EcIdent.name m)
      in
      (* FIXME: Assumes is not array, fix later *)
      let size = match EcEnv.Circuit.lookup_bitstring_size (tc1_env tc) v.v_type with
      | Some size -> size
      | None -> tc_error (tc1_penv tc) "Failed to get size for type %a (is it finite and does it have a binding?)" 
        EcPrinting.(pp_type PPEnv.(ofenv (tc1_env tc))) v.v_type
      in
      let tpath = match v.v_type.ty_node with
      | Tconstr (p, _ ) -> p
      | _ -> tc_error (tc1_penv tc) "Failed to destructure var type"
      in
      let of_int = match EcEnv.Circuit.reverse_type (tc1_env tc) tpath with
      | [] -> tc_error (tc1_penv tc) "No bindings found for type of var"
      | `Bitstring { ofint }::_ -> ofint
      | _ -> tc_error (tc1_penv tc) "FIXME: Unhandled case"
      in
      let ngoals = 1 lsl size in
(*       let ngoals = min ngoals 5 in *)
      List.init ngoals (fun i ->  (* FIXME FIXME this is bad *)
        let subst = EcPV.PVM.(add (tc1_env tc) (PVloc v.v_name) m 
        (EcTypesafeFol.f_app_safe (tc1_env tc) of_int [f_int BI.(of_int i)]) empty)
        in
        let s = subst_pv_stmt (tc1_hyps tc) m subst hs_s in
        let subst = EcPV.PVM.subst (tc1_env tc) subst in
        let pr = subst hs_pr in
        let po = subst hs_po in
        let goal = f_hoareS mt ({inv=pr;m}) s ({inv=po;m}) in
        if debug then 
        (
        Format.eprintf "[W] Generated goal %d@." i;
(*
        Format.eprintf "%a@." 
        EcPrinting.(pp_form PPEnv.(ofenv (tc1_env tc))) goal
*)
        );
        goal
      )

    | _ -> tc_error (tc1_penv tc) "Wrong goal shape@."
    in

    match do_all goals with
    | None -> 
      EcEnv.notify ~immediate:true (tc1_env tc) `Warning "[W] Extens took %f seconds@." (Unix.gettimeofday () -. tm);
      close (tcenv_of_tcenv1 tc) VBdep
    | Some gfail ->
      tc_error (tc1_penv tc) "Failed to close goal:@. %a@." 
      EcPrinting.(pp_form PPEnv.(ofenv (tc1_env tc))) gfail
        false


