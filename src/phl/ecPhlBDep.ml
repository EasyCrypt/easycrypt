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
open LDecl

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


let int_of_form (hyps: hyps) (f: form) : BI.zint = 
  match f.f_node with 
  | Fint i -> i
  | _ -> destr_int @@ EcCallbyValue.norm_cbv EcReduction.full_red hyps f

(* -------------------------------------------------------------------- *)
let mapreduce 
  (hyps : hyps) 
  ((mem, mt): memenv) 
  (proc: stmt) 
  ((invs, n): variable list * int) 
  ((outvs, m) : variable list * int) 
  (f: psymbol) 
  (pcond: psymbol)
  (perm: (int -> int) option)
  : unit =


  let time (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    Format.eprintf "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in
  let tm = Unix.gettimeofday () in
  
  let env = toenv hyps in
  let ppenv = EcPrinting.PPEnv.ofenv env in
  let fpth, _fo = EcEnv.Op.lookup ([], f.pl_desc) env in
  let f = EcTypesafeFol.fop_from_path env fpth in
  let fc = circuit_of_form hyps f in
  let fc = circuit_flatten fc in
  let fc = circuit_aggregate_inps fc in

  let tm = time tm "Lane function circuit generation done" in
  
  (* let () = Format.eprintf "len %d @." (List.length fc.circ) in *)
  (* let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in *)
  (* let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps fmt) (HL.deps fc.circ |> Array.to_list) in *)
  let pcond_pth, _pcondo = EcEnv.Op.lookup ([], pcond.pl_desc) env in
  let pcond = EcTypesafeFol.fop_from_path env pcond_pth in
  let pcondc = circuit_of_form hyps pcond in
  let pcondc = circuit_flatten pcondc in
  let pcondc = circuit_aggregate_inps pcondc in
  (* let () = Format.eprintf "pcondc output size: %d@." (List.length pcondc.circ) in *)

  
  let tm = time tm "Precondition circuit generation done" in
  
  let pstate : (symbol, circuit) Map.t = Map.empty in

  let inps = List.map (EcCircuits.input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) invs in
  let pstate = List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 
  in
  
  let pstate = List.fold_left (EcCircuits.process_instr hyps mem) pstate proc.s_node in
  let pstate = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate in

  let tm = time tm "Program circuit generation done" in

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
    (* let c = match perm with *) 
    (* | None -> c *)
    (* | Some perm -> circuit_permutation (size_of_circ c.circ) m perm *)
    (* in *)
    (* let c = circuit_aggregate_inps c in *) 
    (* let () = List.iter2 (fun c v -> Format.eprintf "%s inputs: " v.v_name; *)
      (* List.iter (Format.eprintf "%s ") (List.map cinput_to_string c.inps); *)
      (* Format.eprintf "@."; ) [c] outvs in *)
    let cs = circuit_mapreduce c n m in
    let cs = match perm with
      | None -> cs
      | Some perm -> List.init (List.length cs) (fun i -> List.nth cs (perm i))
    in

    let tm = time tm "circuit dependecy analysis + splitting done" in

    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) cs;
    Format.eprintf "Pcond: %s@." (circuit_to_string pcondc);
    let () = try 
      assert (List.for_all (fun c -> circ_equiv ~strict:true (List.hd cs) c (Some pcondc)) (List.tl cs));
      with Assert_failure _ as e ->
        Format.eprintf "Program lane equivalence failed between lanes@.";
        raise e
    in

    let tm = time tm "Program lanes equivs done" in

    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) cs;
    Format.eprintf "Lane func: %s@." (circuit_to_string fc);
    
    assert(circ_equiv (List.hd cs) fc (Some pcondc));

    let _tm = time tm "Program to lane func equiv done" in
    
    Format.eprintf "Success@."
  end 


(* -------------------------------------------------------------------- *)
let prog_equiv_prod 
  (hyps : hyps) 
  ((meml, mtl), (memr, mtr): memenv * memenv) 
  (proc_l, proc_r: stmt * stmt) 
  ((invs_l, invs_r, n): (variable list * variable list * int))
  ((outvs_l, outvs_r, m) : (variable list * variable list * int))
  (pcond : form option)
  (preprocess : bool ): unit =
  let env = toenv hyps in
  
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

  let pcond = Option.map (circuit_of_form hyps) pcond in

  let time (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    Format.eprintf "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in
  let tm = Unix.gettimeofday () in
  
  let pstate_l = List.fold_left (EcCircuits.process_instr hyps meml) pstate_l proc_l.s_node in
  let pstate_l = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate_l in

  let tm = time tm "Left program generation done" in
  
  let pstate_r = List.fold_left (EcCircuits.process_instr hyps memr) pstate_r proc_r.s_node in
  let pstate_r = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate_r in

  let tm = time tm "Right program generation done" in
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
    let tm = time tm "Preprocessing for mapreduce done" in
    let lanes_l = circuit_mapreduce c_l n m in
    let tm = time tm "Left program deps + split done" in
    let lanes_r = circuit_mapreduce c_r n m in
    let tm = time tm "Right program deps + split done" in
    Format.eprintf "Left program lanes: @.";
    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) lanes_l;
    Format.eprintf "Right program lanes: @.";
    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) lanes_l;
    let success : bool = if preprocess then
        (if (List.for_all (fun c -> circ_equiv ~strict:true (List.hd lanes_l) c pcond) (List.tl lanes_l)) then
        let tm = time tm "Left program lanes equiv done" in
        (if (List.for_all (fun c -> circ_equiv ~strict:true (List.hd lanes_r) c pcond) (List.tl lanes_r)) then
        let tm = time tm "Right program lanes equiv done" in
        (if (circ_equiv ~strict:true (List.hd lanes_l) (List.hd lanes_r) pcond) then
        (let tm = time tm "First lanes equiv done" in
         ignore tm; true) else false
        ) else false
        ) else false
        )
    else
      if (List.for_all2 (fun c_l c_r -> circ_equiv ~strict:true c_l c_r pcond) lanes_l lanes_r) then
      let tm = time tm "Lane equivs done" in
      (ignore tm; true)
      else false
    in
    assert success;
    Format.eprintf "Success@."
  end 

(*
  Input: pstate -> Map from program variables to circuits, possibly empty
         hyps
         form -> form to be processed
  Output: 
    Form with equalities between bitstring replaced by true
    if both sides are equivalent as circuits 
    or false otherwise
*)
let rec circ_simplify_form_bitstring_equality
  ?(mem = mhr) 
  ?(pstate: (symbol, circuit) Map.t = Map.empty) 
  ?(pcond: circuit option)
  ?(inps: cinput list option)
  (hyps: hyps) 
  (f: form)
  : form =
  let env = toenv hyps in

  let rec check (f : form) =
    match sform_of_form f with
    | SFeq (f1, f2)
         when (Option.is_some @@ EcEnv.Circuit.lookup_bitstring env f1.f_ty)
           || (Option.is_some @@ EcEnv.Circuit.lookup_array env f1.f_ty)
      ->
      let c1 = circuit_of_form ~pstate hyps f1 in
      let c2 = circuit_of_form ~pstate hyps f2 in
      let c1, c2 = match inps with
        | Some inps -> {c1 with inps = inps}, {c2 with inps = inps}
        | None -> c1, c2
      in
      Format.eprintf "[W]Testing circuit equivalence for forms:
      %a@.%a@.With circuits: %s | %s@."
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f1
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f2
      (circuit_to_string c1)
      (circuit_to_string c2);
      f_bool (circ_equiv c1 c2 pcond)
    | _ -> f_map (fun ty -> ty) check f 
  in check f

let circ_form_eval_plus_equiv 
  ?(mem = mhr) 
  (hyps: hyps) 
  (proc: stmt) 
  (invs: variable list) 
  (f: form) 
  (v : variable) 
  : bool = 
  assert(f.f_ty = tbool);
  let env = toenv hyps in
  let redmode = circ_red hyps in
  let (@@!) = EcTypesafeFol.f_app_safe env in
  let inps = List.map (EcCircuits.input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  let size, of_int = match EcEnv.Circuit.lookup_bitstring env v.v_type with
  | Some {size; ofint} -> size, ofint 
  | None -> Format.eprintf "Binding not found for variable %s of type %a@."
    v.v_name (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) v.v_type; assert false
  in
  let rec test_values (size: int) (cur: BI.zint) : bool =
    Format.eprintf "[W] Testing for var = %s@." (BI.to_string cur);
    if Z.numbits (BI.to_zt cur) > size then
    true
    else
    let cur_val = of_int @@! [f_int cur] in 
    let pstate : (symbol, circuit) Map.t = Map.empty in
    let pstate = List.fold_left2
      (fun pstate inp v -> Map.add v inp pstate)
      pstate inpcs (invs |> List.map (fun v -> v.v_name))
    in
    let insts = List.map (fun i -> 
      match i.i_node with
      | Sasgn (lv, e) -> 
        let f = form_of_expr mem e in
        let f = EcPV.PVM.subst1 env (PVloc v.v_name) mem cur_val f in
        let f = EcCallbyValue.norm_cbv redmode hyps f in
        let e = expr_of_form mem f in
        EcCoreModules.i_asgn (lv,e)
      | _ -> i
      ) proc.s_node 
    in
    let pstate = List.fold_left (EcCircuits.process_instr hyps mem) pstate insts in
    let pstate = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate in
    let f = EcPV.PVM.subst1 env (PVloc v.v_name) mem cur_val f in
    let pcond = match Map.find_opt v.v_name pstate with
      | Some circ -> Some (circuit_ueq circ (circuit_of_form hyps cur_val))
      | None -> None
    in
    let () = Format.eprintf "Form before circuit simplify %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f in
    let f = EcCallbyValue.norm_cbv redmode hyps f in
    let f = circ_simplify_form_bitstring_equality ~mem ~pstate ~inps ?pcond hyps f in
    let f = EcCallbyValue.norm_cbv (EcReduction.full_red) hyps f in
    if f <> f_true then
    (Format.eprintf "Got %a after reduction@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f;
    false)
    else
    test_values size (BI.(add cur one))
  in
  test_values size (BI.zero)

(* -------------------------------------------------------------------- *)
let mapreduce_eval
  (hyps : hyps) 
  ((mem, mt): memenv) 
  (proc: stmt) 
  ((invs, n): variable list * int) 
  ((outvs, m) : variable list * int) 
  (f: psymbol) 
  (range: form list)
  (sign: bool)
  : unit =


  let time (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    Format.eprintf "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in
  let tm = Unix.gettimeofday () in
  
  let env = toenv hyps in
  let fc = EcEnv.Op.lookup ([], f.pl_desc) env |> fst in
  let (@@!) = EcTypesafeFol.f_app_safe env in 

  let tm = time tm "Lane function circuit generation done" in
  
  (* let () = Format.eprintf "len %d @." (List.length fc.circ) in *)
  (* let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in *)
  (* let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps fmt) (HL.deps fc.circ |> Array.to_list) in *)

  
  let tm = time tm "Precondition circuit generation done" in
  
  let pstate : (symbol, circuit) Map.t = Map.empty in

  let inps = List.map (EcCircuits.input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) invs in
  let pstate = List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 
  in
  
  let pstate = List.fold_left (EcCircuits.process_instr hyps mem) pstate proc.s_node in
  let pstate = Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate in

  let tm = time tm "Program circuit generation done" in

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
    (* let c = match perm with *) 
    (* | None -> c *)
    (* | Some perm -> circuit_permutation (size_of_circ c.circ) m perm *)
    (* in *)
    (* let c = circuit_aggregate_inps c in *) 
    (* let () = List.iter2 (fun c v -> Format.eprintf "%s inputs: " v.v_name; *)
      (* List.iter (Format.eprintf "%s ") (List.map cinput_to_string c.inps); *)
      (* Format.eprintf "@."; ) [c] outvs in *)
    let cs = circuit_mapreduce c n m in

    let tm = time tm "circuit dependecy analysis + splitting done" in

    List.iter (fun c -> Format.eprintf "%s@." (circuit_to_string c)) cs;
    let () = try 
      assert (List.for_all (fun c -> circ_equiv ~strict:true (List.hd cs) c None) (List.tl cs));
      with Assert_failure _ as e ->
        Format.eprintf "Program lane equivalence failed between lanes@.";
        raise e
    in

    let tm = time tm "Program lanes equivs done" in


    assert(List.for_all (fun v ->
      let fv = v in
      let v = destr_int v in 
      let lane_val = fc @@! [fv] in
      let lane_val = int_of_form hyps lane_val in
      let circ_val = compute ~sign (List.hd cs) [v] in
      if BI.((of_int circ_val) = lane_val) then true else
      (Format.eprintf "Error on input %s@.Circ val:%d | Lane val: %s@." (BI.to_string v)
      circ_val (BI.to_string lane_val); 
      false)
    ) range);

    let _tm = time tm "Program to lane func equiv done" in
    
    Format.eprintf "Success@."
  end 


 
(* FIXME UNTESTED *)
let circ_hoare (hyps : hyps) cache ((mem, me): memenv) (pre: form) (proc: stmt) (post: form) : unit =
  let pstate, inps = EcCircuits.pstate_of_memtype (LDecl.toenv hyps) me in
  
  let pre_c = circuit_of_form ~pstate ~cache hyps pre in
  let pstate = List.fold_left (EcCircuits.process_instr hyps mem ~cache) pstate proc.s_node in
  let post_c = EcCircuits.circuit_of_form ~pstate ~cache hyps post in
  
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
let circ_goal (hyps: hyps) (cache: _) (f: form) : unit = 
  
  let f_c = circuit_of_form ~cache hyps f in
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
  | FhoareS sF -> circ_hoare (FApi.tc1_hyps tc) cache sF.hs_m sF.hs_pr sF.hs_s sF.hs_po
  
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false

  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false

  | FequivF _ -> assert false
  | FequivS _ -> assert false

  | FeagerF _ -> assert false

  | Fpr _ -> assert false
  | _ when f.f_ty = tbool -> circ_goal (FApi.tc1_hyps tc) cache f
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
  match EcEnv.Circuit.lookup_array_and_bitstring env f.f_ty with
  | Some ({ tolist }, {type_; to_=tb}) -> 
    let base = tconstr type_ [] in
    let w2bits = w2bits_op env base in
    EcCoreLib.CI_List.p_flatten @@!
    [EcCoreLib.CI_List.p_map @@! [w2bits; (tolist @@! [f])]]
  | None -> 
    w2bits env f.f_ty f

let reconstruct_from_bits (env: env) (f: form) (t: ty) =
  (* Check input is a bool list *)
  assert (match f.f_ty.ty_node with
  | Tconstr(p, [b]) when p = EcCoreLib.CI_List.p_list -> b = tbool
  | _ -> false);
  let (@@!) = EcTypesafeFol.f_app_safe env in
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({ oflist }, {type_; size; ofint}) -> 
    let base = tconstr type_ [] in
    oflist @@! [ ofint @@! [f_int (BI.of_int 0)];
    EcCoreLib.CI_List.p_map @@! [ bits2w_op env base;
    EcCoreLib.CI_List.p_chunk @@! [(f_int (BI.of_int size)); f]]]
  | _ -> 
    bits2w env t f

let reconstruct_from_bits_op (env: env) (t: ty) =
  (* Check input is a bool list *)
  let (@@!) = EcTypesafeFol.f_app_safe env in
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({ oflist }, {type_; size; ofint}) -> 
    let base = tconstr type_ [] in
    let temp = create "temp" in
    let bool_list = tconstr EcCoreLib.CI_List.p_list [tbool] in
    f_quant Llambda [(temp, GTty bool_list)] @@
    oflist @@! [ ofint @@! [f_int (BI.of_int 0)];
    EcCoreLib.CI_List.p_map @@! [ bits2w_op env base;
    EcCoreLib.CI_List.p_chunk @@! [(f_int (BI.of_int size)); f_local temp bool_list]]]
  | _ -> 
    bits2w_op env t
   
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
  | FhoareS sF -> mapreduce (FApi.tc1_hyps tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op pcond perm
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

  (* FIXME: remove shortcircuit *)
  (* if true then *)
    (* let hr = EcLowPhlGoal.tc1_as_hoareS tc in *)
    (* let outvs  = get_vars outvs hr.hs_m in *)
    (* let inpvs = get_vars inpvs hr.hs_m in *)
    (* let tc = EcPhlConseq.t_hoareS_conseq_nm f_true f_true tc in *)
    (* FApi.t_last (t_bdep n m inpvs outvs pcond lane None) tc *) 
  (* else *)
  
  let (@@!) pth args = 
    try
      EcTypesafeFol.f_app_safe env pth args 
    with EcUnify.UnificationFailure _ ->
      Format.eprintf "Type mismatch in pre-post generation, check your lane and precondition types@.";
      raise BDepError
  in

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
  (* FIXME: Add a check that this does not return a function type 
    aka lane function only have one argument *)
  let inpbty, outbty = tfrom_tfun2 olane.op_ty in
  
  (* Refactor this *)
  
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in

  

  (* ------------------------------------------------------------------ *)
  let outvs  = get_vars outvs hr.hs_m in
  let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) outvs in
  let poutvs = List.map (flatten_to_bits env) poutvs in
  let poutvs = List.rev poutvs in
  let poutvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty) in
  let poutvs = EcCoreLib.CI_List.p_flatten @@! [poutvs] in
  let poutvs = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int m); poutvs] in
  let poutvs = EcCoreLib.CI_List.p_map @@! [(reconstruct_from_bits_op env outbty); poutvs] in

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
  let finpvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) inpvs in
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
  let finvs = List.map (fun id -> f_local id inty) invs in
  let pinvs = List.map (flatten_to_bits env) finvs in
  let pinvs = List.rev pinvs in
  let pinvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) (List.rev pinvs) (fop_empty (List.hd pinvs).f_ty) in
  let pinvs = EcCoreLib.CI_List.p_flatten @@! [pinvs] in
  let () = Format.eprintf "Type after flatten %a@." pp_type pinvs.f_ty in
  let pinvs = EcCoreLib.CI_List.p_chunk @@! [f_int (BI.of_int n); pinvs] in
  let () = Format.eprintf "Type after chunk %a@." pp_type pinvs.f_ty in
  let b2w = (reconstruct_from_bits_op env inpbty) in
  let () = Format.eprintf "Type of b2w %a@." pp_type b2w.f_ty in
  let pinvs = EcCoreLib.CI_List.p_map @@! [b2w; pinvs] in
  let () = Format.eprintf "Type after first map %a@." pp_type pinvs.f_ty in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [(f_op plane [] olane.op_ty); pinvs] in
  (* A REFACTOR EVERYTHING HERE A *)
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinvs_post poutvs in
  let pre = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinvs] in

  assert (List.compare_lengths inpvs invs = 0);
  let pre = f_ands (pre::(List.map2 (fun iv ipv -> f_eq iv ipv) finvs finpvs)) in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_hoareS_conseq_nm pre post tc in
  FApi.t_last (t_bdep n m inpvs outvs pcond lane fperm) tc 



let t_bdepeq (inpvs_l, inpvs_r: (variable list * variable list)) (n: int) (out_blocks: (int * variable list * variable list) list) (pcond: form option) (preprocess: bool) (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FequivF sE -> assert false
  | FequivS sE -> List.iter (fun (m, outvs_l, outvs_r) ->
    prog_equiv_prod (FApi.tc1_hyps tc) (sE.es_ml, sE.es_mr) (sE.es_sl, sE.es_sr) (inpvs_l, inpvs_r, n) (outvs_l, outvs_r, m) pcond preprocess) out_blocks
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
  let preprocess = bdeinfo.preprocess in

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

      (* let pinpr_blocks = List.map (flatten_to_bits env) pinpvsr in *)
      (* let pinpr_blocks = List.rev pinpr_blocks in *)
      (* let pinpr_blocks = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) pinpr_blocks (fop_empty (List.hd pinpr_blocks).f_ty)  in *)
      (* let pinpr_blocks = EcCoreLib.CI_List.p_flatten @@! [pinpr_blocks] in *)
      (* let pinpr_blocks = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int n); pinpr_blocks] in *)
      (* let pinpr_blocks = EcCoreLib.CI_List.p_map @@! [(bits2w_op env opinty); pinpr_blocks] in *)

      let pre_l = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpl_blocks] in

      (* let pre_r = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpr_blocks] in *)

      (* let pre = f_and pre_l pre_r in *)
      let pre = pre_l in

      pre, Some pcond
    | None -> pre, None
  in

  let pre = f_and pre prepcond in
  
  (* ------------------------------------------------------------------ *)
  let tc = EcPhlConseq.t_equivS_conseq_nm pre post tc in
  FApi.t_last (t_bdepeq (inpvsl, inpvsr) n outvs pcond preprocess) tc 

let t_bdep_form 
  (invs: variable list)
  (f: form)
  (v: variable)
  (tc : tcenv1)
  : tcenv =
  match (FApi.tc1_goal tc).f_node with
  | FhoareF sH -> assert false
  | FhoareS sF -> if (circ_form_eval_plus_equiv ~mem:(fst sF.hs_m) (FApi.tc1_hyps tc) sF.hs_s invs f v) then
    let new_sF = {sF with hs_po=f_imp f sF.hs_po} in
    FApi.xmutate1 tc VBdep [f_hoareS_r new_sF]
    else 
    (Format.eprintf "Supplied formula is not always true@.";
    assert false)
  | _ -> assert false

let process_bdep_form 
  (invs: bdepvar list)
  (f: pformula)
  (v: bdepvar)
  (tc : tcenv1)
  : tcenv =
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in
  let hyps = FApi.tc1_hyps tc in
  let invs = get_vars invs hr.hs_m in
  let v = get_var v hr.hs_m |> as_seq1 in
  let ue = EcUnify.UniEnv.create None in
  let env = (toenv hyps) in
  let env = Memory.push_active hr.hs_m env in
  let f = EcTyping.trans_prop env ue f in
  assert (EcUnify.UniEnv.closed ue);
  let f = EcCoreSubst.Fsubst.f_subst (Tuni.subst (EcUnify.UniEnv.close ue)) f in
  t_bdep_form invs f v tc

let form_list_from_iota (hyps: hyps) (f: form) : form list =
  match f.f_node with
  | Fapp ({f_node = Fop(p, _)}, [n; m]) when p = EcCoreLib.CI_List.p_iota ->
    let n = int_of_form hyps n in
    let m = int_of_form hyps m in
    List.init (BI.to_int m) (fun i -> f_int (BI.(add n (of_int i))))
  | _ -> assert false

let t_bdep_eval
  (n: int) 
  (m: int) 
  (inpvs: variable list) 
  (outvs: variable list) 
  (op: psymbol) 
  (range: form list) 
  (sign: bool)
  (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FhoareF sH -> assert false  
  | FhoareS sF -> mapreduce_eval (FApi.tc1_hyps tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op range sign
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep

let process_bdep_eval (bdeinfo: bdep_eval_info) (tc: tcenv1) =
  let { in_ty; out_ty; invs; inpvs; outvs; lane; range; sign } = bdeinfo in

  let env = FApi.tc1_env tc in
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in
  let hyps = FApi.tc1_hyps tc in
  let ppenv = EcPrinting.PPEnv.ofenv env in

  (* FIXME: remove shortcircuit *)
  (* if true then *)
    (* let hr = EcLowPhlGoal.tc1_as_hoareS tc in *)
    (* let outvs  = get_vars outvs hr.hs_m in *)
    (* let inpvs = get_vars inpvs hr.hs_m in *)
    (* let tc = EcPhlConseq.t_hoareS_conseq_nm f_true f_true tc in *)
    (* FApi.t_last (t_bdep n m inpvs outvs pcond lane None) tc *) 
  (* else *)
  
  let (@@!) pth args = 
    try
      EcTypesafeFol.f_app_safe env pth args 
    with EcUnify.UnificationFailure _ ->
      Format.eprintf "Type mismatch in pre-post generation, check your lane and precondition types@.
      Args: %a@." (fun fmt fs -> List.iter 
      (fun f -> (Format.fprintf fmt "%a | "(EcPrinting.pp_form ppenv) f)) fs) args;
      raise BDepError
  in
  let (@@!!) pth args = 
    try
      EcTypesafeFol.f_app_safe ~full:false env pth args 
    with EcUnify.UnificationFailure _ ->
      Format.eprintf "Type mismatch in pre-post generation, check your lane and precondition types@.";
      raise BDepError
  in

  (* DEBUG SECTION *)
  let pp_type (fmt: Format.formatter) (ty: ty) =
    Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
  
  let plane, olane = EcEnv.Op.lookup ([], lane.pl_desc) env in
  (* let inpbty, outbty = tfrom_tfun2 olane.op_ty in *)
  let in_ty =
    let ue = EcUnify.UniEnv.create None in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue in_ty in
    assert (EcUnify.UniEnv.closed ue);
    ty_subst (Tuni.subst (EcUnify.UniEnv.close ue)) ty 
  in
  let out_ty =
    let ue = EcUnify.UniEnv.create None in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue out_ty in
    assert (EcUnify.UniEnv.closed ue);
    ty_subst (Tuni.subst (EcUnify.UniEnv.close ue)) ty 
  in

  let ue = EcUnify.UniEnv.create None in
  let env = Memory.push_active hr.hs_m env in
  let range = EcTyping.trans_form env ue range (tconstr EcCoreLib.CI_List.p_list [tint])in
  assert (EcUnify.UniEnv.closed ue);
  let range = EcCoreSubst.Fsubst.f_subst (Tuni.subst (EcUnify.UniEnv.close ue)) range in

  let frange = form_list_from_iota hyps range in


  let n, in_to_uint, in_to_sint,in_of_int = match EcEnv.Circuit.lookup_bitstring env in_ty with
  | Some {size; touint; tosint; ofint} -> size, touint, tosint, ofint
  | _ -> Format.eprintf "No binding for type %a@." pp_type in_ty; raise BDepError
  in
  let in_to_uint = f_op in_to_uint [] (tfun in_ty tint) in
  let in_to_sint = f_op in_to_sint [] (tfun in_ty tint) in
  let in_of_int = f_op in_of_int [] (tfun tint in_ty) in
  let m, out_of_int = match EcEnv.Circuit.lookup_bitstring env out_ty with
  | Some {size; ofint} -> size, ofint 
  | _ -> Format.eprintf "No binding for type %a@." pp_type out_ty; raise BDepError
  in
  let out_of_int = f_op out_of_int [] (tfun tint out_ty) in
  
 
  if false then 
  let inpvs = get_vars inpvs hr.hs_m in
  let outvs  = get_vars outvs hr.hs_m in
  let tc = EcPhlConseq.t_hoareS_conseq_nm f_true f_false tc in
  FApi.t_last (t_bdep_eval n m inpvs outvs lane frange sign) tc 

  else
  (* ------------------------------------------------------------------ *)
  let outvs  = get_vars outvs hr.hs_m in
  let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) outvs in
  let poutvs = List.map (flatten_to_bits env) poutvs in
  let poutvs = List.rev poutvs in
  let poutvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty) in
  let poutvs = EcCoreLib.CI_List.p_flatten @@! [poutvs] in
  let poutvs = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int m); poutvs] in
  let poutvs = EcCoreLib.CI_List.p_map @@! [(reconstruct_from_bits_op env out_ty); poutvs] in

  
  (* ------------------------------------------------------------------ *)
  let inpvs = get_vars inpvs hr.hs_m in
  let finpvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) inpvs in
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
  let finvs = List.map (fun id -> f_local id inty) invs in
  let pinvs = List.map (flatten_to_bits env) finvs in
  let pinvs = List.rev pinvs in
  let pinvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) (List.rev pinvs) (fop_empty (List.hd pinvs).f_ty) in
  let pinvs = EcCoreLib.CI_List.p_flatten @@! [pinvs] in
  let () = Format.eprintf "Type after flatten %a@." pp_type pinvs.f_ty in
  let pinvs = EcCoreLib.CI_List.p_chunk @@! [f_int (BI.of_int n); pinvs] in
  let () = Format.eprintf "Type after chunk %a@." pp_type pinvs.f_ty in
  let b2w = (reconstruct_from_bits_op env in_ty) in
  let () = Format.eprintf "Type of b2w %a@." pp_type b2w.f_ty in
  let pinvs = EcCoreLib.CI_List.p_map @@! [b2w; pinvs] in
  let () = Format.eprintf "Type after first map %a@." pp_type pinvs.f_ty in
  let pinvs_post = if sign 
    then EcCoreLib.CI_List.p_map @@! [in_to_sint; pinvs] 
    else EcCoreLib.CI_List.p_map @@! [in_to_uint; pinvs] 
  in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [(f_op plane [] olane.op_ty); pinvs_post] in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [out_of_int; pinvs_post] in
  (* A REFACTOR EVERYTHING HERE A *)
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinvs_post poutvs in
  let pre = EcCoreLib.CI_List.p_all @@! 
    [(EcCoreLib.CI_List.p_mem @@!! [
      (EcCoreLib.CI_List.p_map @@! [in_of_int; range])]); pinvs] in

  assert (List.compare_lengths inpvs invs = 0);
  let pre = f_ands (pre::(List.map2 (fun iv ipv -> f_eq iv ipv) finvs finpvs)) in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_hoareS_conseq_nm pre post tc in
  FApi.t_last (t_bdep_eval n m inpvs outvs lane frange sign) tc 


