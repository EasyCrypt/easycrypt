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
open EcCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.Hlaig
end

exception BDepError

(* -------------------------------------------------------------------- *)
let mapreduce 
  (env : env) 
  ((mem, mt): memenv) 
  (proc: stmt) 
  ((invs, n): variable list * int) 
  ((outvs, m) : variable list * int) 
  (f: psymbol) 
  (pcond: psymbol)
  (perm: (int -> int) option)
  : unit =
  
  let f = EcEnv.Op.lookup ([], f.pl_desc) env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> failwith "Invalid operator type" in
  let fc = circuit_of_form env f in
  (* let () = Format.eprintf "len %d @." (List.length fc.circ) in *)
  (* let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in *)
  (* let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps fmt) (HL.deps fc.circ |> Array.to_list) in *)
  let pcondc = EcEnv.Op.lookup ([], pcond.pl_desc) env |> snd in
  let pcondc = match pcondc.op_kind with
  | OB_oper (Some (OP_Plain pcondc)) -> pcondc
  | _ -> failwith "Invalid operator type" in
  let pcondc = circuit_of_form env pcondc in
  (* let () = Format.eprintf "pcondc output size: %d@." (List.length pcondc.circ) in *)
  
  let pstate : (symbol, circuit) Map.t = Map.empty in

  let inps = List.map (EcCircuits.input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) invs in
  let pstate = List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 
  in
  
  let pstate = List.fold_left (EcCircuits.process_instr env mem) pstate proc.s_node in
  let pstate = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate in
  begin 
    let circs = List.map (fun v -> Option.get (Map.find_opt v pstate)) (List.map (fun v -> v.v_name) outvs) in
    let () = List.iter2 (fun c v -> Format.eprintf "%s inputs: " v.v_name;
      List.iter (Format.eprintf "%s ") (List.map cinput_to_string c.inps);
      Format.eprintf "@."; ) circs outvs in
    let () = List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) circs in
    assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs = 1);
    let cinp = (List.hd circs).inps in
    let c = {(circuit_aggregate circs) with inps=cinp} in

    (* OPTIONAL PERMUTATION STEP *)
    let c = match perm with 
    | None -> c
    | Some perm -> circuit_permutation (size_of_circ c.circ) m perm
    in
    (* let c = circuit_aggregate_inps c in *) 
    (* let () = List.iter2 (fun c v -> Format.eprintf "%s inputs: " v.v_name; *)
      (* List.iter (Format.eprintf "%s ") (List.map cinput_to_string c.inps); *)
      (* Format.eprintf "@."; ) [c] outvs in *)
    let cs = circuit_mapreduce c n m in
    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) cs;
    Format.eprintf "Pcond: %s@." (circuit_to_string pcondc);
    let () = assert(List.for_all (fun c -> circ_equiv ~strict:true (List.hd cs) c (Some pcondc)) (List.tl cs)) in
    Format.eprintf "Lane func: %s@." (circuit_to_string fc);
    let () = assert(circ_equiv (List.hd cs) fc (Some pcondc)) in
    Format.eprintf "Success@."
  end 


(* -------------------------------------------------------------------- *)
let prog_equiv_prod 
  (env : env) 
  ((meml, mtl), (memr, mtr): memenv * memenv) 
  (proc_l, proc_r: stmt * stmt) 
  ((invs_l, invs_r, n): (variable list * variable list * int))
  ((outvs_l, outvs_r, m) : (variable list * variable list * int))
  (pcond : form option): unit =
  let pstate_l : (symbol, circuit) Map.t = Map.empty in
  let pstate_r : (symbol, circuit) Map.t = Map.empty in

  let inps = List.map (EcCircuits.input_of_variable env) invs_l in
  let inpcs, inps = List.split inps in
  let pstate_l = List.fold_left2
    (fun pstate inp v -> Map.add v inp pstate)
    pstate_l inpcs (invs_l |> List.map (fun v -> v.v_name))
  in
  let pstate_r = List.fold_left2
    (fun pstate inp v -> Map.add v inp pstate)
    pstate_r inpcs (invs_r |> List.map (fun v -> v.v_name))
  in

  let pcond = Option.map (circuit_of_form env) pcond in

  let pstate_l = List.fold_left (EcCircuits.process_instr env meml) pstate_l proc_l.s_node in
  let pstate_l = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate_l in
  let pstate_r = List.fold_left (EcCircuits.process_instr env memr) pstate_r proc_r.s_node in
  let pstate_r = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate_r in
  begin 
    let circs_l = List.map (fun v -> Option.get (Map.find_opt v pstate_l)) 
                  (List.map (fun v -> v.v_name) outvs_l) in
    let circs_r = List.map (fun v -> Option.get (Map.find_opt v pstate_r)) 
                  (List.map (fun v -> v.v_name) outvs_r) in
                
    (* let () = List.iter2 (fun c v -> Format.eprintf "%s inputs: " v.v_name; *)
      (* List.iter (Format.eprintf "%s ") (List.map cinput_to_string c.inps); *)
      (* Format.eprintf "@."; ) circs outvs in *)
    
    (* let () = List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) circs in *)
    assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs_l = 1);
    assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs_r = 1);
    let cinp_l = (List.hd circs_l).inps in
    let cinp_r = (List.hd circs_r).inps in
    let c_l = {(circuit_aggregate circs_l) with inps=cinp_l} in
    let c_r = {(circuit_aggregate circs_r) with inps=cinp_r} in
    let lanes_l = circuit_mapreduce c_l n m in
    let lanes_r = circuit_mapreduce c_r n m in
    Format.eprintf "Left program lanes: @.";
    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) lanes_l;
    Format.eprintf "Right program lanes: @.";
    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) lanes_l;
    let () = assert (List.for_all2 (fun c_l c_r -> circ_equiv ~strict:true c_l c_r pcond) lanes_l lanes_r) in
    Format.eprintf "Success@."
  end 



(* FIXME UNTESTED *)
let circ_hoare (env : env) cache ((mem, me): memenv) (pre: form) (proc: stmt) (post: form) : unit =
  let pstate, inps = EcCircuits.pstate_of_memtype env me in
  
  let pre_c = circuit_of_form ~pstate ~cache env pre in
  let pstate = List.fold_left (EcCircuits.process_instr env mem ~cache) pstate proc.s_node in
  let post_c = EcCircuits.circuit_of_form ~pstate ~cache env post in
  
  (* DEBUG PRINTS *)
  (* List.iter (fun fc -> *)
  (* let namer = fun id -> *) 
    (* List.find_opt (fun inp -> tag (fst inp) = id) fc.inps *) 
    (* |> Option.map fst |> Option.map name |> Option.default (string_of_int id) in *)
  (* let () = Format.eprintf "Out len: %d @." (List.length fc.circ) in *)
  (* let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%s %d@." (fst x |> namer) (snd x)) in *)
  (* let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps ~namer fmt) (HL.deps fc.circ |> Array.to_list) in *)
  (* let () = Format.eprintf "Args for circuit: "; *) 
            (* List.iter (fun (idn, w) -> Format.eprintf "(%s, %d) " idn.id_symb w) fc.inps; *)
            (* Format.eprintf "@." in *)
  (* ()) [post_c]; *)

  Format.eprintf "Inputs: "; List.iter (Format.eprintf "%s ") (List.map cinput_to_string post_c.inps);
  Format.eprintf "@."; 
  if EcCircuits.circ_check post_c (Some pre_c) then (Format.eprintf "Success") else 
  raise BDepError
  
(* FIXME UNTESTED *)
let circ_goal (env: env) (cache: _) (f: form) : unit = 
  
  let f_c = circuit_of_form ~cache env f in
  begin
  assert (EcCircuits.circ_check f_c None);
  end

let t_circ (tc: tcenv1) : tcenv =
  let hyps = LDecl.tohyps (FApi.tc1_hyps tc) in
  let vs = List.filter_map (function 
    | idn, EcBaseLogic.LD_var (ty, _) -> 
      begin try
      let inp = cinput_of_type ~idn (FApi.tc1_env tc) ty in
    Some (idn, (inp, {(circ_ident inp) with inps=[]}))
      with CircError _ -> None
      end
    | _ -> None
    ) hyps.h_local in
  let cache = Map.of_seq @@ List.to_seq vs in
  
  
  let f = (FApi.tc1_goal tc) in
  let () = match f.f_node with
  | FhoareF sH -> assert false
  | FhoareS sF -> circ_hoare (FApi.tc1_env tc) cache sF.hs_m sF.hs_pr sF.hs_s sF.hs_po
  
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false

  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false

  | FequivF _ -> assert false
  | FequivS _ -> assert false

  | FeagerF _ -> assert false

  | Fpr _ -> assert false
  | _ when f.f_ty = tbool -> circ_goal (FApi.tc1_env tc) cache f
  | _ -> Format.eprintf "f has type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv (FApi.tc1_env tc))) f.f_ty;
    raise BDepError
  in
  FApi.close (!@ tc) VBdep



  let w2bits_new (env: env) (ty: ty) (arg: form) : form = 
    let (@@!) = EcTypesafeFol.f_app_safe env in
    match EcEnv.Circuit.lookup_array env ty with
    | Some {tolist;} -> let bty = match ty.ty_node with
      | Tconstr (p, [bty]) -> bty
      | _ -> failwith "Wrong type structure for array"
      in let ptb, otb = 
        match EcEnv.Circuit.lookup_bitstring env bty with
        | Some {to_=tb; _} -> tb, EcEnv.Op.by_path tb env
        | _ -> Format.eprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
      in EcCoreLib.CI_List.p_flatten @@! [
        EcCoreLib.CI_List.p_map @@! [f_op ptb [] otb.op_ty; 
        tolist @@! [arg]]
      ]
    | None -> 
      begin match EcEnv.Circuit.lookup_bitstring env ty with
        | Some {to_=tb; _} -> tb @@! [arg]
        | _ -> Format.eprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
      end
  

  let w2bits (env: env) (ty: ty) (arg: form) : form = 
    let tb = match EcEnv.Circuit.lookup_bitstring env ty with
    | Some {to_=tb; _} -> tb
    | _ -> Format.eprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env tb [arg]
  
  let bits2w (env: env) (ty: ty) (arg: form) : form = 
    let fb = match EcEnv.Circuit.lookup_bitstring env ty with
    | Some {from_=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env fb [arg]
  
  let w2bits_op (env: env) (ty: ty) : form = 
    let tb = match EcEnv.Circuit.lookup_bitstring env ty with
    | Some {to_=tb; _} -> tb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let tbp, tbo = EcEnv.Op.lookup (EcPath.toqsymbol tb) env in
    f_op tb [] tbo.op_ty 
  
  let bits2w_op (env: env) (ty: ty) : form = 
    let fb = match EcEnv.Circuit.lookup_bitstring env ty with
    | Some {from_=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let fbp, fbo = EcEnv.Op.lookup (EcPath.toqsymbol fb) env in
    f_op fb [] fbo.op_ty 
  

  let flatten_to_bits (env: env) (f: form) = 
    let (@@!) = EcTypesafeFol.f_app_safe env in
    match EcEnv.Circuit.lookup_array env f.f_ty with
    | Some {tolist; _} -> 
      let base = match f.f_ty.ty_node with
      | Tconstr (_, [b]) -> b
      | _ -> assert false
      in 
      let w2bits = w2bits_op env base in
      EcCoreLib.CI_List.p_flatten @@!
      [EcCoreLib.CI_List.p_map @@! [w2bits; (tolist @@! [f])]]
    | None -> 
      w2bits env f.f_ty f
      
let t_bdep 
  (n: int) 
  (m: int) 
  (inpvs: variable list) 
  (outvs: variable list) 
  (pcond: psymbol) 
  (op: psymbol) 
  (perm: (int -> int) option) 
  (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FhoareF sH -> assert false  
  | FhoareS sF -> mapreduce (FApi.tc1_env tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op pcond perm
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep

let get_var (v : bdepvar) (m : memenv) : variable list =
  let get1 (v : symbol) =
    match EcMemory.lookup_me v m with
    | Some (v, None, _) -> v
    | _ -> Format.eprintf "Couldn't locate variable %s@." v; assert false in

  match v with
  | `Var v ->
      [get1 (unloc v)]
  | `VarRange (v, n) ->
      List.init n (fun i -> get1 (Format.sprintf "%s_%d" (unloc v) n))

let get_vars (vs : bdepvar list) (m : memenv) : variable list =
  List.flatten (List.map (fun v -> get_var v m) vs)

let process_bdep (bdinfo: bdep_info) (tc: tcenv1) =
  let { m; n; invs; inpvs; outvs; lane; pcond; perm } = bdinfo in

  let env = FApi.tc1_env tc in
  let (@@!) pth args = EcTypesafeFol.f_app_safe env pth args in

  let fperm, pperm = match perm with 
  | None -> None, None
  | Some perm -> 
    let pperm = EcEnv.Op.lookup ([], perm.pl_desc) env |> fst in
    let fperm (i: int) = 
      let arg = f_int (BI.of_int i) in
      let call = EcTypesafeFol.f_app_safe env pperm [arg] in
      let res = EcCallbyValue.norm_cbv (EcReduction.full_red) (FApi.tc1_hyps tc) call in
      destr_int res |> BI.to_int
    in
    Some fperm, Some pperm
  in

  (* DEBUG SECTION *)
  let pp_type (fmt: Format.formatter) (ty: ty) =
    Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
  
  let plane, olane = EcEnv.Op.lookup ([], lane.pl_desc) env in
  let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
  let inpbty, outbty = tfrom_tfun2 olane.op_ty in
  
  (* Refactor this *)
  
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in

  

  (* ------------------------------------------------------------------ *)
  let outvs  = get_vars outvs hr.hs_m in
  let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) outvs in
  let poutvs = List.map (flatten_to_bits env) poutvs in
  let poutvs = List.rev poutvs in
  let poutvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty)  in
  let poutvs = EcCoreLib.CI_List.p_flatten @@! [poutvs] in
  let poutvs = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int m); poutvs] in
  let poutvs = EcCoreLib.CI_List.p_map @@! [(bits2w_op env outbty); poutvs] in

  (* OPTIONAL PERMUTATION STEP *)
  let poutvs = match pperm with 
  | None -> poutvs
  | Some pperm -> 
    let i = (create "i", GTty tint) in
    let bty = tfrom_tlist poutvs.f_ty in
    EcCoreLib.CI_List.p_mkseq @@! [
      f_lambda [i] 
        (EcCoreLib.CI_List.p_nth @@! [f_op EcCoreLib.CI_Witness.p_witness [bty] bty; poutvs; 
          pperm @@! [f_local (fst i) tint]]);
      EcCoreLib.CI_List.p_size @@! [poutvs]
    ]
  in
  
  
  (* ------------------------------------------------------------------ *)
  let inpvs = get_vars inpvs hr.hs_m in
  (* let pinpvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) inpvs in *)
  let invs, inv_tys =
    let lookup (x : bdepvar) : (ident * ty) list =
      let get1 (v : symbol) =
        EcEnv.Var.lookup_local v env in

      match x with
      | `Var x ->
          [get1 (unloc x)]
      | `VarRange (x, n) ->
          List.init n (fun i -> get1 (Format.sprintf "%s_%d" (unloc x) i)) in 
    List.map lookup invs |> List.flatten |> List.split in
  let inty = match List.collapse inv_tys with
  | Some ty -> ty
  | None -> Format.eprintf "Failed to coallesce types for input@."; raise BDepError
  in
  let invs = List.map (fun id -> f_local id inty) invs in
  let pinpvs = List.map (flatten_to_bits env) invs in
  let pinpvs = List.rev pinpvs in
  let pinpvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) (List.rev pinpvs) (fop_empty (List.hd pinpvs).f_ty) in
  let pinpvs = EcCoreLib.CI_List.p_flatten @@! [pinpvs] in
  let () = Format.eprintf "Type after flatten %a@." pp_type pinpvs.f_ty in
  let pinpvs = EcCoreLib.CI_List.p_chunk @@! [f_int (BI.of_int n); pinpvs] in
  let () = Format.eprintf "Type after chunk %a@." pp_type pinpvs.f_ty in
  let b2w = (bits2w_op env inpbty) in
  let () = Format.eprintf "Type of b2w %a@." pp_type b2w.f_ty in
  let pinpvs = EcCoreLib.CI_List.p_map @@! [b2w; pinpvs] in
  let () = Format.eprintf "Type after first map %a@." pp_type pinpvs.f_ty in
  let pinpvs_post = EcCoreLib.CI_List.p_map @@! [(f_op plane [] olane.op_ty); pinpvs] in
  (* A REFACTOR EVERYTHING HERE A *)
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinpvs_post poutvs in
  let pre = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpvs] in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_hoareS_conseq_nm pre post tc in
  FApi.t_last (t_bdep n m inpvs outvs pcond lane fperm) tc 



let t_bdepeq (inpvs_l, inpvs_r: (variable list * variable list)) (n: int) (out_blocks: (int * variable list * variable list) list) (pcond: form option) (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FequivF sE -> assert false
  | FequivS sE -> List.iter (fun (m, outvs_l, outvs_r) ->
    prog_equiv_prod (FApi.tc1_env tc) (sE.es_ml, sE.es_mr) (sE.es_sl, sE.es_sr) (inpvs_l, inpvs_r, n) (outvs_l, outvs_r, m) pcond) out_blocks
  | FhoareF sH -> assert false  
  | FhoareS sF -> assert false
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep

let process_bdepeq 
  (bdeinfo: bdepeq_info)
  (tc: tcenv1) 
=

  let env = FApi.tc1_env tc in
  let (@@!) pth args = EcTypesafeFol.f_app_safe env pth args in


  let inpvsl = bdeinfo.inpvs_l in
  let inpvsr = bdeinfo.inpvs_r in
  let n = bdeinfo.n in

  (* DEBUG SECTION *)
    
  let eqS = EcLowPhlGoal.tc1_as_equivS tc in
  let mem_l, mem_r = eqS.es_ml, eqS.es_mr in

  (* ------------------------------------------------------------------ *)
  let process_block (outvsl: bdepvar list) (outvsr: bdepvar list) = 
    let outvsl = get_vars outvsl mem_l in
    let poutvsl = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_l)) outvsl in

    let outvsr = get_vars outvsr mem_r in
    let poutvsr = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_r)) outvsr in
    List.map2 f_eq poutvsl poutvsr |> f_ands, (outvsl, outvsr)
  in
   

  let inpvsl = get_vars inpvsl mem_l in
  let pinpvsl = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_l)) inpvsl in

  let inpvsr = get_vars inpvsr mem_r in
  let pinpvsr = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_r)) inpvsr in

  let pre = List.map2 f_eq pinpvsl pinpvsr |> f_ands in
  let post, outvs = List.map (fun (m, vs_l, vs_r) -> 
    let post, outvs = process_block vs_l vs_r in 
    let outvs_l, outvs_r = outvs in
    post, (m, outvs_l, outvs_r)) bdeinfo.out_blocks |> List.split in
  let post = f_ands post in
  
  
  let prepcond, pcond = match bdeinfo.pcond with
    | Some pcond -> 
      (* FIXME: generate correct precond *) 
      let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
      let pcond = match opcond.op_kind with
        | OB_oper (Some OP_Plain f) -> f
        | _ -> failwith "Unsupported precondition kind for bdepeq"
      in

      let opinty = 
        match opcond.op_ty.ty_node with
      | Tfun (a, b) -> a
      | _ -> failwith "precond should have function type"
      in
      
      let pinpl_blocks = List.map (flatten_to_bits env) pinpvsl in
      let pinpl_blocks = List.rev pinpl_blocks in
      let pinpl_blocks = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) pinpl_blocks (fop_empty (List.hd pinpl_blocks).f_ty)  in
      let pinpl_blocks = EcCoreLib.CI_List.p_flatten @@! [pinpl_blocks] in
      let pinpl_blocks = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int n); pinpl_blocks] in
      let pinpl_blocks = EcCoreLib.CI_List.p_map @@! [(bits2w_op env opinty); pinpl_blocks] in

      let pinpr_blocks = List.map (flatten_to_bits env) pinpvsr in
      let pinpr_blocks = List.rev pinpr_blocks in
      let pinpr_blocks = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) pinpr_blocks (fop_empty (List.hd pinpr_blocks).f_ty)  in
      let pinpr_blocks = EcCoreLib.CI_List.p_flatten @@! [pinpr_blocks] in
      let pinpr_blocks = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int n); pinpr_blocks] in
      let pinpr_blocks = EcCoreLib.CI_List.p_map @@! [(bits2w_op env opinty); pinpr_blocks] in

      let pre_l = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpl_blocks] in

      let pre_r = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpr_blocks] in

      let pre = f_and pre_l pre_r in

      pre, Some pcond
    | None -> pre, None
  in

  let pre = f_and pre prepcond in
  
  (* ------------------------------------------------------------------ *)
  let tc = EcPhlConseq.t_equivS_conseq_nm pre post tc in
  FApi.t_last (t_bdepeq (inpvsl, inpvsr) n outvs pcond) tc 
