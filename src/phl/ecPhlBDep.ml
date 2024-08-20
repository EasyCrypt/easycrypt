(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcTypes
open EcModules
open EcCoreGoal
open EcAst
open EcCoreFol
open EcIdent
open EcCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_avx2.FromSpec ()
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.HLAig
end


exception BDepError
(* -------------------------------------------------------------------- *)
let mapreduce (env : env) ((mem, mt): memenv) (proc: stmt) ((invs, n): variable list * int) ((outvs, m) : variable list * int) (f: psymbol) (pcond: psymbol) : unit =
  let f = EcEnv.Op.lookup ([], f.pl_desc) env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let fc = circuit_of_form env f in
  (* let () = Format.eprintf "len %d @." (List.length fc.circ) in *)
  (* let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%d %d@." (fst x) (snd x)) in *)
  (* let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps fmt) (HL.deps fc.circ |> Array.to_list) in *)
  let pcondc = EcEnv.Op.lookup ([], pcond.pl_desc) env |> snd in
  let pcondc = match pcondc.op_kind with
  | OB_oper (Some (OP_Plain (pcondc, _))) -> pcondc
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
  assert false;
  begin 
    let circs = List.map (fun v -> Option.get (Map.find_opt v pstate)) (List.map (fun v -> v.v_name) outvs) in
    (* let () = List.iteri (fun i circ -> *)
    (* let namer tag = List.find (fun (id, w) -> id.id_tag = tag) circ.inps |> fst |> name in *)
    (* let bdeps = HL.deps circ.circ |> HL.block_deps in *)
      (* Format.eprintf "rp_%d_0 circuit blocks: " i; *)
    (* Format.eprintf "%a@." (fun fmt b -> HL.pp_bdeps ~namer fmt b) bdeps *)
      (* ) circs in *)

    (* FIXME: fix line below *)
    (* let circ = circuit_concat circs in *)

    (* let namer tag = List.find (fun (id, w) -> id.id_tag = tag) circ.inps |> fst |> name in *)
    (* let bdeps = HL.deps circ.circ |> HL.block_deps in *)
      (* Format.eprintf "Proc circuit blocks: "; *)
    (* let () = Format.eprintf "%a@." (fun fmt b -> HL.pp_bdeps ~namer fmt b) bdeps in *)

    (* FIXME: fix line below *)
    (* let circs = circuit_block_split n m circ in *)

    let () = assert (List.for_all (fun c -> circ_equiv (List.hd circs) c (Some pcondc)) (List.tl circs)) in 
    let circ = List.hd circs in

    (* FIXME: fix line below *)
    (* let () = assert (circ_equiv {circ with circ=C.uextend ~size:(List.length fc.circ) circ.circ} fc (Some pcondc)) in *)
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
    
let t_bdep (outvs: variable list) (n: int) (inpvs: variable list) (m: int) (op: psymbol) (pcond: psymbol) (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FhoareF sH -> assert false  
  | FhoareS sF -> mapreduce (FApi.tc1_env tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op pcond
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep
  
let process_bdep 
  ((inpvs, invs, n): string list * string list * int) 
  ((outvs, m): string list * int) 
  (op: psymbol) 
  (pcond: psymbol) 
  (tc: tcenv1) 
=

  let env = FApi.tc1_env tc in
  let f_app_safe = EcTypesafeFol.f_app_safe in

  (* DEBUG SECTION *)
  (* let pp_type (fmt: Format.formatter) (ty: ty) = Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in *)
  
  let get_var (v: symbol) (m: memenv) : variable =
    match EcMemory.lookup_me v m with
    | Some (v, None, _) -> v
    | _ -> Format.eprintf "Couldn't locate variable %s@." v; assert false
  in
  let collapse (xs: 'a list) : 'a option = 
    match xs with
    | [] -> None
    | x::[] -> Some x
    | x::xs -> if List.for_all ((=) x) xs then Some x else None
  in
  let pop, oop = EcEnv.Op.lookup ([], op.pl_desc) env in
  let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
  let inpbty, outbty = tfrom_tfun2 oop.op_ty in
  
  (* Refactor this *)
  let w2bits (ty: ty) (arg: form) : form = 
    let tb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {to_bits=tb; _} -> tb
    | _ -> Format.eprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env tb [arg]
  in
  let bits2w (ty: ty) (arg: form) : form = 
    let fb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {from_bits=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in EcTypesafeFol.f_app_safe env fb [arg]
  in
  let w2bits_op (ty: ty) : form = 
    let tb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {to_bits=tb; _} -> tb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let tbp, tbo = EcEnv.Op.lookup (EcPath.toqsymbol tb) env in
    f_op tb [] tbo.op_ty 
  in
  let bits2w_op (ty: ty) : form = 
    let fb = match EcEnv.Circ.lookup_bitstring env ty with
    | Some {from_bits=fb; _} -> fb
    | _ -> Format.eprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty; assert false
    in let fbp, fbo = EcEnv.Op.lookup (EcPath.toqsymbol fb) env in
    f_op fb [] fbo.op_ty 
  in

  let hr = EcLowPhlGoal.tc1_as_hoareS tc in

  (* ------------------------------------------------------------------ *)
  let outvs = List.map (fun v -> get_var v hr.hs_m) outvs in
  let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) outvs in
  let poutvs = List.map (w2bits (List.hd poutvs).f_ty) poutvs in
  let poutvs = List.rev poutvs in
  let poutvs = List.fold_right (fun v1 v2 -> f_app_safe env EcCoreLib.CI_List.p_cons [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty)  in
  let poutvs = f_app_safe env EcCoreLib.CI_List.p_flatten [poutvs] in
  let poutvs = f_app_safe env (EcCoreLib.CI_List.p_chunk) [f_int (BI.of_int m); poutvs] in
  let poutvs =  EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_map [(bits2w_op outbty); poutvs] in

  
  (* ------------------------------------------------------------------ *)
  let inpvs = List.map (fun v -> get_var v hr.hs_m) inpvs in
  (* let pinpvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)) inpvs in *)
  let invs, inv_tys = List.map (fun v -> EcEnv.Var.lookup_local v env) invs |> List.split in
  let inty = match collapse inv_tys with
  | Some ty -> ty
  | None -> Format.eprintf "Failed to coallesce types for input@."; raise BDepError
  in
  let invs = List.map (fun id -> f_local id inty) invs in
  let pinpvs = List.map (w2bits inty) invs in
  let pinpvs = List.rev pinpvs in
  let pinpvs = List.fold_right (fun v1 v2 -> f_app_safe env EcCoreLib.CI_List.p_cons [v1; v2]) (List.rev pinpvs) (fop_empty (List.hd pinpvs).f_ty) in
  let pinpvs = f_app_safe env EcCoreLib.CI_List.p_flatten [pinpvs] in
  (* let () = Format.eprintf "Type after flatten %a@." pp_type pinpvs.f_ty in *)
  let pinpvs = f_app_safe env EcCoreLib.CI_List.p_chunk [f_int (BI.of_int n); pinpvs] in
  (* let () = Format.eprintf "Type after chunk %a@." pp_type pinpvs.f_ty in *)
  let b2w = (bits2w_op inpbty) in
  (* let () = Format.eprintf "Type of b2w %a@." pp_type b2w.f_ty in *)
  let pinpvs =  EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_map [b2w; pinpvs] in
  (* let () = Format.eprintf "Type after first map %a@." pp_type pinpvs.f_ty in *)
  let pinpvs_post = EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_map [(f_op pop [] oop.op_ty); pinpvs] in
  (* A REFACTOR EVERYTHING HERE A *)
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinpvs_post poutvs in
  let pre = EcTypesafeFol.f_app_safe env EcCoreLib.CI_List.p_all [(f_op ppcond [] opcond.op_ty); pinpvs] in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_conseq pre post tc in
  FApi.t_last (t_bdep outvs n inpvs m op pcond) tc 

(* CODE STORAGE - DO NOT TOUCH *)


(* ----------------------------------------------------------------------- *)
(* FIXME: standardize this, maybe move to common EC lib *)
let op_is_arr_get (p: path) : bool =
  match (EcPath.toqsymbol p) with
  | ["Top"; thr; _], "_.[_]" when String.starts_with thr "Array" -> true
  | _ -> false
  
let op_is_arr_set (p: path) : bool =
  match (EcPath.toqsymbol p) with
  | ["Top"; thr; _], "_.[_<-_]" when String.starts_with thr "Array"  -> true
  | _ -> false

let destruct_array_get (env: env) (f: form) : form * form =
  match f.f_node with 
  | Fapp ({f_node=Fop (p, ty)}, [arr;{f_ty=t_int} as i]) when op_is_arr_get p ->
    arr, i
  | _ -> raise (DestrError "Not an array get")

let destruct_array_set (env: env) (f: form) : form * BI.zint * form =
  match f.f_node with 
  | Fapp ({f_node=Fop (p, ty)}, [arr;{f_node=Fint i; f_ty=t_int}; v]) when op_is_arr_set p ->
    arr, i, v
  | _ -> raise (DestrError "Not an array set (with fixed index)")
  
let destruct_nested_array_set (env: env) (f: form) : form * (BI.zint * form) list = 
  let rec doit acc f =
    try
      let arr, i, v = destruct_array_set env f in
      doit ((i, v)::acc) arr
    with
      | DestrError _ -> f, acc
  in
  let arr, i, v = destruct_array_set env f in
  doit [(i,v)] arr

type init_variant =
| INIT
| MAP

let destruct_array_init (f: form) : form = 
  let p = function
  | _, "init" -> true
  | _ -> false in
  let p pth = p (EcPath.toqsymbol pth) in
  destr_app1 ~name:"init" p f


let destruct_arr_chnk_init (f: form) : form * form * form * init_variant =
  let fn = destruct_array_init f in
  match fn.f_node with
  | Fquant _ -> let binds, fb = destr_lambda fn in
    begin
    match fb.f_node with
    (* map variant *)    
    | Fapp (f, [{f_node=Fapp (chnk, [arr;_i])}]) -> (f, chnk, arr, MAP) 
    (* init variant *)
    | Fapp (f, [{f_node=Fapp (chnk, [arr;_i])}; {f_ty=tint}]) -> (f, chnk, arr, INIT)
    | _ -> failwith "Unsupported form of init body"
    end
  | _ -> failwith "Only lambda init supported"

let chunk_access (env: env) (f: path) (idx: zint) : zint Set.t =
  let o = EcEnv.Op.by_path f env in
  let fb = match o.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Unknown op type"
  in
  let i, fb = match fb.f_node with
  | Fquant (_, [arr; (i, i_ty)], f) -> 
    (i, f)
  | _ -> failwith "Wrong form for chunk"
  in
  let subst = EcSubst.add_flocal EcSubst.empty i (f_int idx) in
  let eval_form = 
    fun f -> (EcReduction.simplify EcReduction.full_red (EcEnv.LDecl.init env []) 
    (EcSubst.subst_form subst f)
    |> destr_int
  ) in
  match fb.f_node with
  | Ftuple fs -> List.fold_left (fun acc i -> 
    let i = (destruct_array_get env i |> snd) in
    let i = eval_form i in
    Set.add i acc) Set.empty fs
  | Fapp _ -> let i = fb in (* FIXME: write better code here *)
    let i = (destruct_array_get env i |> snd) in
    let i = eval_form i in
    Set.singleton i
  | _ -> failwith "Chunk should return tuple"

let const_index_accesses_from_form (env: env) (f: form) : zint Set.t =
  let rec doit (f: form) =
  begin
    let res = try
      let arr, i = destruct_array_get env f in
      let i = destr_int i in
      Set.singleton i
    with 
    | DestrError e when e = "destr_int" ->
      failwith "Non-constant array access"
    | DestrError e -> 
      (* Improve this later *)
      match f.f_node with
      | Fint _ -> Set.empty
      | Fop _ -> Set.empty
      | Fproj (f, _) -> doit f
      | Ftuple args 
      | Fapp (_, args) -> List.fold_left (Set.union) Set.empty (List.map doit args)
      | Fif (cond, ft, ff) -> let ca = doit cond in
        let ta = doit ft in
        let tf = doit ff in
        if (Set.equal ta tf) then Set.union ca ta 
        else begin match (EcReduction.simplify EcReduction.full_red (LDecl.init env []) cond).f_node with
        | Fop (p, _) when p = EcCoreLib.CI_Bool.p_true -> Set.union ca ta
        | Fop (p, _) when p = EcCoreLib.CI_Bool.p_false -> Set.union ca tf
        | _ -> failwith "Non-closed if condition with different array accesses in branches"
        end      
      | _ -> Format.eprintf "%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f; 
        failwith "Uncaught case for const idx array access"
    in res
  end 
  in doit f

(* ----------------------------------------------------------------------- *)
let auto_init (env: env) (f: form) =
  let arr_f, init_f = destr_eq f in
  let arr, asgns = try
    destruct_nested_array_set env arr_f
    with
    | DestrError _ -> Format.eprintf "arr: %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) arr_f;
      raise (DestrError "Not an array on left side") (* FIXME: improve error handling *)
  in 
  let f, chnk, arr, init_var = destruct_arr_chnk_init init_f in
  assert (List.is_unique ~eq:BI.equal (List.fst asgns));
  let chnk, _tys = destr_op chnk in
  (* TODO: Replace above by sort (order-preserving) + unique pass ?*)
  List.iter (fun (i, f) -> 
    let chunk = chunk_access env chnk i in
    let arr = const_index_accesses_from_form env f in
    if not (Set.subset arr chunk) then
    begin
     Format.eprintf "arr accesses: @.";
     Set.iter (Format.eprintf "%s ") (Set.map BI.to_string arr);
     Format.eprintf "chunk accesses: @.";
     Set.iter (Format.eprintf "%s ") (Set.map BI.to_string chunk);
     Format.eprintf "@."
    end;
     assert(Set.subset arr chunk)) asgns;
  let rs_b = destruct_array_init init_f in
  match destr_lambda rs_b with
  | ([(i, i_ty)], rs_f) -> 
  let eval_rs (idx: zint) = 
    let subst = EcSubst.add_flocal (EcSubst.empty) i (f_int idx) in
    EcSubst.subst_form subst rs_f
  in
  List.map (fun (idx, f) -> f_eq f (eval_rs idx)) asgns |> List.fold_left (fun a b -> EcTypesafeFol.f_app_safe env (EcEnv.Op.lookup_path ([], "/\\") env) [a;b]) (f_true)
  | _ -> assert false
  
  
  
  (* Right side checks TODO *)
  (* Array safety checks TODO *)
 
