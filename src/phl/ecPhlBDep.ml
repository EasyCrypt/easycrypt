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
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.Hlaig
end

exception BDepError of string
exception BDepUninitializedInputs

(* TODO: Refactor error printing and checking? Lots of duplicated code *)

let int_of_form (hyps: hyps) (f: form) : BI.zint = 
  match f.f_node with 
  | Fint i -> i
  | _ -> begin try destr_int @@ EcCallbyValue.norm_cbv EcReduction.full_red hyps f with 
    | DestrError _ -> let err = Format.asprintf "Failed to reduce form to int: %a@."
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (toenv hyps))) f in
      raise (BDepError err)
    end

let time (env: env) (t: float) (msg: string) : float =
  let new_t = Unix.gettimeofday () in
  EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. t);
  new_t

let circ_of_qsymbol (hyps: hyps) (qs: qsymbol) : hyps * circuit =
  try
    let env = toenv hyps in

    let fpth, _fo = EcEnv.Op.lookup qs env in
    let f = EcTypesafeFol.fop_from_path env fpth in
    let f = EcCallbyValue.norm_cbv (EcCircuits.circ_red hyps) hyps f in
    
    let hyps, fc = circuit_of_form hyps f in
    let fc = circuit_flatten fc in
    let fc = circuit_aggregate_inps fc in
    hyps, fc
  with CircError err ->
    raise (BDepError err)
 
(* 
   f => arr_t.init (fun i => f.(i + offset)) 
  Assumes f has an array type binding
  Assumes f has enough positions so that 
  arr_t.size + offset < size f (as array)
*)
let array_init_from_form (env: env) (f: form) ((arr_t, offset): qsymbol * BI.zint) : form =
  let ppe = EcPrinting.PPEnv.ofenv env in
  let tpath = match EcEnv.Ty.lookup_opt arr_t env with
  | None -> raise (BDepError "Failed to lookup type for input slice")
  | Some (path, decl) when List.length decl.tyd_params = 1 ->
    path
  | Some ((_path, decl) as tdecl) ->
    raise (BDepError (Format.asprintf "Type given to input slice (%a) does not look like an array type" EcPrinting.(pp_typedecl ppe) tdecl))
  in
  let get = match EcEnv.Circuit.lookup_array env f.f_ty with
  | Some { get } -> get
  | None -> raise (BDepError (Format.asprintf "Failed to lookup array binding for type %a" EcPrinting.(pp_type ppe) f.f_ty))
  in
  let init = EcEnv.Op.lookup_path (fst (tpath |> EcPath.toqsymbol), "init") env in
  let idx = create "i" in
  let f = f_lambda [(idx, GTty tint)] 
    (EcTypesafeFol.f_app_safe env get [f; f_int_add (f_local idx tint) (f_int offset)]) 
  in EcTypesafeFol.f_app_safe env init [f]

(* -------------------------------------------------------------------- *)
let mapreduce 
  ?(debug: bool = false)
  (hyps : hyps) 
  ((mem, mt): memenv) 
  (proc: stmt) 
  ((invs, n): (variable * (int * int) option) list * int) 
  ((outvs, m) : (variable * (int * int) option) list * int) 
  (f: psymbol) 
  (pcond: psymbol)
  (perm: (int -> int) option)
  : unit =

  let tm = Unix.gettimeofday () in
  let env = toenv hyps in
  
  (* ------------------------------------------------------------------ *)
  let hyps, fc = try 
    circ_of_qsymbol hyps ([], f.pl_desc) 
    with BDepError err -> 
      raise (BDepError ("Lane function circuit generation failed with error:\n" ^ err))
  in
  if debug then EcEnv.notify ~immediate:true env `Warning "Writing lane function to file %s...@." @@ circuit_to_file ~name:"lane_function" fc;

  let tm = time env tm "Lane function circuit generation done" in
  
  (* ------------------------------------------------------------------ *)
  let hyps, pcondc = try 
    circ_of_qsymbol hyps ([], pcond.pl_desc) 
    with BDepError err ->
      raise (BDepError ("Precondition circuit generation failed with error:\n" ^ err))
  in
  if debug then EcEnv.notify ~immediate:true env `Warning "Writing precondition function to file %s...@." @@ circuit_to_file ~name:"pcond" pcondc;
 
  let tm = time env tm "Precondition circuit generation done" in
  
  (* ------------------------------------------------------------------ *)
  let pinvs = List.fst invs in
  let hyps, st = try 
    EcCircuits.state_of_prog hyps mem proc.s_node pinvs 
  with CircError err ->
    raise (BDepError err)
  in

  let tm = time env tm "Program circuit generation done" in

  begin 
    let circs = List.map (function 
      | {v_name}, None -> Option.get (state_get_opt st mem v_name)
      | {v_name}, Some (sz, offset) ->
        circuit_slice (Option.get (state_get_opt st mem v_name)) sz offset
      ) 
      outvs 
    in
    Format.eprintf "Circs[0] = %a@." pp_circuit (List.hd circs);
    Format.eprintf "Program variable names registered:@.";
    List.iter (fun ((m, v), _) -> Format.eprintf "%s{%s}@." v (name m)) (state_get_all_pv st);
    List.iteri (fun i c -> match circuit_has_uninitialized c with
      | Some j -> EcEnv.notify ~immediate:true env `Critical "Bit %d of input %d has a dependency on an unititialized input@." j i; raise BDepUninitializedInputs
      | None -> ()) circs;

    (* This is required for now as we do not allow mapreduce with multiple arguments *)
    (* assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs = 1); *)    

    (* ------------------------------------------------------------------ *)
    let circs = 
      try 
        let slcs = List.snd invs in
(*         if List.for_all Option.is_none slcs then circs else  *)
        List.map (fun c -> 
            (circuit_align_inputs c slcs)
          ) circs
      with CircError _ -> 
        raise (BDepError "Failed to align inputs to slice")
    in


    (* ------------------------------------------------------------------ *)
    let c = try 
      (circuit_aggregate circs)
      with CircError _ ->
        raise (BDepError "Failed to concatenate outputs")
    in

    let c = try
      (circuit_aggregate_inps c)
      with CircError _ ->
        raise (BDepError "Failed to concatenate outputs")
    in

    if debug then EcEnv.notify ~immediate:true env `Info "Writing program circuit before mapreduce to file %s...@." @@ circuit_to_file ~name:"prog_no_mapreduce" c;

    (* ------------------------------------------------------------------ *)
    let cs = try 
      circuit_mapreduce ?perm c n m 
      with CircError err ->
        raise (BDepError err)
    in

    let tm = time env tm "circuit dependecy analysis + splitting done" in

    if debug then EcEnv.notify ~immediate:true env `Info "Writing lane 0 circit to file %s...@." @@ circuit_to_file ~name:"lane_0" (List.hd cs);

    (* ------------------------------------------------------------------ *)
    List.iteri (fun i c -> 
    if debug then EcEnv.notify ~immediate:true env `Info "Writing lane %d circit to file %s...@." (i+1) @@ circuit_to_file ~name:("lane_" ^ (string_of_int (i+1))) c;
    if circ_equiv ~pcond:pcondc (List.hd cs) c 
      then ()
      else let err = Format.sprintf "Equivalence check failed between lanes 0 and %d" (i+1) 
        in raise (BDepError err)) 
    (List.tl cs);

    let tm = time env tm "Program lanes equivs done" in
    
    (* ------------------------------------------------------------------ *)
    if circ_equiv ~pcond:pcondc (List.hd cs) fc then () 
    else raise (BDepError "Equivalence failed between lane 0 and lane function");

    let _tm = time env tm "Program to lane func equiv done" in
    
    EcEnv.notify ~immediate:true env `Info "Success@."
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

  (* ------------------------------------------------------------------ *)
  let hyps, pcond = match pcond with
    | Some pcond -> begin try 
      let hyps, c = circuit_of_form hyps pcond in
      hyps, Some c
    with CircError err ->
      raise (BDepError err)
    end
    | None -> hyps, None
  in
  let tm = Unix.gettimeofday () in
  
  (* ------------------------------------------------------------------ *)
  let (hyps, st_l) : hyps * state = try
    EcCircuits.state_of_prog hyps meml proc_l.s_node invs_l 
  with CircError err ->
    raise (BDepError err)
  in
  let tm = time env tm "Left program generation done" in

  (* ------------------------------------------------------------------ *)
  let (hyps, st_r) : hyps * state = try
    EcCircuits.state_of_prog hyps memr proc_r.s_node invs_l 
  with CircError err ->
    raise (BDepError err)
  in
  let tm = time env tm "Right program generation done" in

  begin 
    (* ------------------------------------------------------------------ *)
    let circs_l = List.map (fun v -> state_get st_l meml v) 
                  (List.map (fun v -> v.v_name) outvs_l) in
    let circs_r = List.map (fun v -> state_get st_r memr v) 
                  (List.map (fun v -> v.v_name) outvs_r) in

    List.iteri (fun i c -> match circuit_has_uninitialized c with
      | Some j -> EcEnv.notify ~immediate:true env `Critical "Bit %d of input %d of the left program has a dependency on an unititialized input@." j i; raise BDepUninitializedInputs
      | None -> ()) circs_l;

    List.iteri (fun i c -> match circuit_has_uninitialized c with
      | Some j -> EcEnv.notify ~immediate:true env `Critical "Bit %d of input %d of the right program has a dependency on an unititialized input@." j i; raise BDepUninitializedInputs
      | None -> ()) circs_r;

    (*assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs_l = 1); *)
    (*assert (Set.cardinal @@ Set.of_list @@ List.map (fun c -> c.inps) circs_r = 1);*)
    (* ------------------------------------------------------------------ *)
    let c_l = try 
      (circuit_aggregate circs_l)
      with CircError _err ->
        raise (BDepError "Failed to aggregate left program outputs")
    in
    let c_r = try 
      (circuit_aggregate circs_r)
      with CircError _err ->
        raise (BDepError "Failed to aggregate right program outputs")
    in
    (* ------------------------------------------------------------------ *)
    let c_r = try 
      (circuit_aggregate_inps c_r)
      with CircError _err ->
        raise (BDepError "Failed to aggregate right program inputs")
    in
    let c_l = try 
      (circuit_aggregate_inps c_l)
      with CircError _err ->
        raise (BDepError "Failed to aggregate right program inputs")
    in

    let tm = time env tm "Preprocessing for mapreduce done" in

    (* ------------------------------------------------------------------ *)
    let lanes_l = try 
      circuit_mapreduce c_l n m 
      with CircError err ->
        raise (BDepError ("Left program split step failed with error:\n" ^ err))
    in
    let tm = time env tm "Left program deps + split done" in

    let lanes_r = try 
      circuit_mapreduce c_r n m 
      with CircError err ->
        raise (BDepError ("Right program split step failed with error:\n" ^ err))
    in
    let tm = time env tm "Right program deps + split done" in

    if preprocess then
      begin
        (* ------------------------------------------------------------------ *)
        (List.iteri (fun i c -> 
          if circ_equiv ?pcond (List.hd lanes_l) c 
          then () 
          else let err = Format.sprintf "Left program lane equiv failed between lanes 0 and %d@." (i+i)
            in raise (BDepError err)) 
        (List.tl lanes_l)); 
        let tm = time env tm "Left program lanes equiv done" in

        (List.iteri (fun i c -> 
          if circ_equiv ?pcond (List.hd lanes_r) c 
          then () 
          else let err = Format.sprintf "Right program lane equiv failed between lanes 0 and %d@." (i+i)
            in raise (BDepError err)) 
        (List.tl lanes_r)); 
        let tm = time env tm "Right program lanes equiv done" in
        
        (* ------------------------------------------------------------------ *)
        if (circ_equiv ?pcond (List.hd lanes_l) (List.hd lanes_r)) 
        then
          time env tm "First lanes equiv done" |> ignore
        else
          raise (BDepError "Lane equiv failed between first lane of left and right programs")
        end
    else
      begin
        List.iter2i (fun i c_l c_r -> 
          if circ_equiv ?pcond c_l c_r 
          then () 
          else let err = Format.sprintf "Lane equivalence failed between programs for lane %d@." i in
            raise (BDepError err)) lanes_l lanes_r;
        time env tm "Program lane equivs done" |> ignore
        end
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

let circ_form_eval_plus_equiv 
  ?(mem: memory option) 
  (hyps: hyps) 
  (proc: stmt) 
  (invs: variable list) 
  (f: form) 
  (v : variable) 
  : bool = 

  let mem = match mem with
  | Some mem -> mem
  | None -> EcIdent.create "&hr"
  in

  (* ------------------------------------------------------------------ *)
  assert(f.f_ty = tbool);

  (* ------------------------------------------------------------------ *)
  let env = toenv hyps in
  let redmode = circ_red hyps in
  let (@@!) = EcTypesafeFol.f_app_safe env in

  (* ------------------------------------------------------------------ *)
  let size, of_int = match EcEnv.Circuit.lookup_bitstring env v.v_type with
  | Some {size=(_, Some size); ofint} -> size, ofint 
  | Some {size=(_, None); ofint} -> 
      raise (BDepError "No concrete binding bitstring size")
  | None -> 
      let err = Format.asprintf "Binding not found for variable %s of type %a@."
        v.v_name (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) v.v_type 
      in raise (BDepError err)
  in

  let rec test_values (size: int) (cur: BI.zint) : bool =
    if debug then EcEnv.notify ~immediate:true env `Info "Testing for var = %s@." (BI.to_string cur);

    (* ------------------------------------------------------------------ *)
    if Z.numbits (BI.to_zt cur) > size then true else (* If we reach the maximum value jump out *) 

    (* ------------------------------------------------------------------ *)
    let cur_bs = of_int @@! [f_int cur] in  (* Current testing value as a bitstring *)

    let insts = List.map (fun i -> 
      match i.i_node with
      | Sasgn (lv, e) -> 
        let f = form_of_expr e in
        let f = EcPV.PVM.subst1 env (PVloc v.v_name) mem cur_bs f in
        let f = EcCallbyValue.norm_cbv redmode hyps f in
        let e = expr_of_form f in
        EcCoreModules.i_asgn (lv, e)
      | _ -> i
      ) proc.s_node 
    in

    let hyps, st = try
      EcCircuits.state_of_prog hyps mem insts invs 
    with CircError err ->
      raise (BDepError err)
    in
    
    (* ------------------------------------------------------------------ *)
    let f = EcPV.PVM.subst1 env (PVloc v.v_name) mem cur_bs f in
    let hyps, pcond = match state_get_opt st mem v.v_name with
      | Some circ -> 
        begin try 
          Option.may (fun i -> 
            EcEnv.notify ~immediate:true env `Critical 
              "Bit %d of precondition circuit has dependency on uninitialized inputs@." i; 
            raise (BDepError "Uninitialized input for circuit")) 
          (circuit_has_uninitialized circ);
          let hyps, c = (circuit_of_form hyps cur_bs) in
          hyps, Some (circuit_ueq circ c)
        with CircError err ->
          raise (BDepError ("Failed to generate circuit for current value precondition with error:\n" ^ err))
        end
      | None -> hyps, None
    in

    (* FIXME: how many times to reduce here ? *)
    (* ------------------------------------------------------------------ *)
    let f = EcCallbyValue.norm_cbv redmode hyps f in
    let f = EcCircuits.circ_simplify_form_bitstring_equality ~st ?pcond hyps f in
    let f = EcCallbyValue.norm_cbv (EcReduction.full_red) hyps f in

    if f <> f_true then
      (EcEnv.notify ~immediate:true env `Critical 
        "Got %a after reduction@." 
        (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f;
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


  let tm = Unix.gettimeofday () in
  
  (* ------------------------------------------------------------------ *)
  let env = toenv hyps in
  let fc = EcEnv.Op.lookup ([], f.pl_desc) env |> fst in
  let (@@!) = EcTypesafeFol.f_app_safe env in 

  let tm = time env tm "Lane function circuit generation done" in
  
  (* ------------------------------------------------------------------ *)
  let hyps, st = try 
    EcCircuits.state_of_prog hyps mem proc.s_node invs 
  with CircError err ->
    raise (BDepError err)
  in

  let tm = time env tm "Program circuit generation done" in

  begin 
    let circs = List.map (fun v -> state_get st mem v) (List.map (fun v -> v.v_name) outvs) in

    List.iteri (fun i c -> match circuit_has_uninitialized c with
      | Some j -> EcEnv.notify ~immediate:true env `Critical "Bit %d of input %d has a dependency on an unititialized input@." j i; raise BDepUninitializedInputs
      | None -> ()) circs;

    (* ------------------------------------------------------------------ *)
    let c = try 
      (circuit_aggregate circs)
      with CircError _err ->
        raise (BDepError "Failed to concatenate program outputs")
    in
    let c = try 
      (circuit_aggregate_inps c)
      with CircError _err ->
        raise (BDepError "Failed to concatenate program outputs")
    in

    (* ------------------------------------------------------------------ *)
    let cs = try 
      circuit_mapreduce c n m 
      with CircError err ->
        raise (BDepError ("Split step failed with error:\n" ^ err))
    in

    let tm = time env tm "circuit dependecy analysis + splitting done" in

    (* ------------------------------------------------------------------ *)
    List.iteri (fun i c -> 
      if circ_equiv (List.hd cs) c 
      then ()
      else let err = Format.sprintf "Equivalence failed between program lanes 0 and %d@." (i + 1) in
        raise (BDepError err)
    )
    (List.tl cs);

    let tm = time env tm "Program lanes equivs done" in

    (* ------------------------------------------------------------------ *)
    List.iter (fun v ->
      let fv = v in
      let v = destr_int v in 
      let lane_val = fc @@! [fv] in
      let lane_val = int_of_form hyps lane_val in
      let circ_val = compute ~sign (List.hd cs) [v] in
      if circ_val = lane_val then () 
      else let err = 
        Format.sprintf "Error on input %s@.Circ val:%s | Lane val: %s@." 
          (BI.to_string v) 
          (BI.to_string circ_val)
          (BI.to_string lane_val) 
      in raise (BDepError err)
    ) range;

    time env tm "Program to lane func equiv done" |> ignore
  end 

let w2bits (env: env) (ty: ty) (arg: form) : form = 
  let tb = match EcEnv.Circuit.lookup_bitstring env ty with
  | Some {to_=tb; _} -> tb
  | _ -> let err = Format.asprintf "No w2bits for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
    raise (BDepError err)
  in EcTypesafeFol.f_app_safe env tb [arg]

let bits2w (env: env) (ty: ty) (arg: form) : form = 
  let fb = match EcEnv.Circuit.lookup_bitstring env ty with
  | Some {from_=fb; _} -> fb
  | _ -> let err = Format.asprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
    raise (BDepError err)
  in EcTypesafeFol.f_app_safe env fb [arg]

let w2bits_op (env: env) (ty: ty) : form = 
  let tb = match EcEnv.Circuit.lookup_bitstring env ty with
  | Some {to_=tb; _} -> tb
  | _ -> let err = Format.asprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
      raise (BDepError err)
  in let tbp, tbo = EcEnv.Op.lookup (EcPath.toqsymbol tb) env in
  f_op tb [] tbo.op_ty 

let bits2w_op (env: env) (ty: ty) : form = 
  let fb = match EcEnv.Circuit.lookup_bitstring env ty with
  | Some {from_=fb; _} -> fb
  | _ -> let err = Format.asprintf "No bits2w for type %a@." (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
      raise (BDepError err)
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
  | Some ({ oflist }, {type_; size = (_, Some size); ofint}) -> 
    let base = tconstr type_ [] in
    oflist @@! [ ofint @@! [f_int (BI.of_int 0)];
    EcCoreLib.CI_List.p_map @@! [ bits2w_op env base;
    EcCoreLib.CI_List.p_chunk @@! [(f_int (BI.of_int size)); f]]]
  | Some ({ oflist }, {type_; size = (_, None); ofint}) -> 
    raise (BDepError "No concrete  binding for type in reconstruct_from_bits") (* FIXME: error messages *)
  | _ -> 
    bits2w env t f

(* FIXME: review and cleanup this section *)

let reconstruct_from_bits_op (env: env) (t: ty) =
  (* Check input is a bool list *)
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({ oflist }, {type_; size = (_, Some size); ofint}) -> 
    let temp = create "temp" in
    let bool_list = tconstr EcCoreLib.CI_List.p_list [tbool] in
    f_quant Llambda [(temp, GTty bool_list)] @@
    reconstruct_from_bits env (f_local temp bool_list) t
  | Some ({ oflist }, {type_; size = (_, None); ofint}) -> 
    raise (BDepError "No concrete  binding for type in reconstruct_from_bits_op") (* FIXME: error messages *)
  | _ -> 
    bits2w_op env t
   
let t_bdep 
  ?(debug: bool = false)
  (n: int) 
  (m: int) 
  (inpvs: ((variable * (int * int) option) list))
  (outvs: ((variable * (int * int) option) list)) 
  (pcond: psymbol) 
  (op: psymbol) 
  (perm: (int -> int) option) 
  (tc : tcenv1) =
  let () = match (FApi.tc1_goal tc).f_node with
  | FhoareS sF -> if true then
    begin try mapreduce ~debug (FApi.tc1_hyps tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op pcond perm with
    | BDepError err -> tc_error (FApi.tc1_penv tc) "%s" err
      end
    else ()
  (* FIXME PR: Should these be guarded before call or do we just fail somehow if we hit it? *)
  | FhoareF sH -> assert false  
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep

let get_var (env: env) (v : bdepvar) (m : memenv) : (variable * ((qsymbol * BI.zint) option)) list =
  let get1 (v : symbol) =
    match EcMemory.lookup_me v m with
    | Some (v, None, _) -> v
    | _ -> let err = Format.asprintf "Couldn't locate variable %s@." v in
      raise (BDepError err)
  in
  match v with
  | `Var v ->
    [get1 (unloc v), None]
  | `VarRange (v, n) ->
    List.init n (fun i -> get1 (Format.sprintf "%s_%d" (unloc v) n), None)
  | `Slice (v, (arr_t, off)) ->
    [get1 (unloc v), Some(unloc arr_t, off)]
    

let get_vars (env: env) (vs : bdepvar list) (m : memenv) : (variable * ((qsymbol * BI.zint) option)) list =
  List.flatten (List.map (fun v -> get_var env v m) vs)

let blocks_from_vars (env: env) (vs: form list) (ty: ty) : form = 
    let (@@!) pth args = 
      try
        EcTypesafeFol.f_app_safe env pth args 
      with EcUnify.UnificationFailure _ ->
        let err = Format.sprintf "Type mismatch in pre-post generation, check your lane and precondition types@." in
        raise (BDepError err)
    in   
    let m = try
      width_of_type env ty
      with CircError err ->
        raise (BDepError ("Error while constructing precondition: \n" ^ err))
    in
    (* let poutvs = List.map (fun v -> EcFol.f_pvar (pv_loc v.v_name) v.v_type mem) vs in *)
    let poutvs = List.map (flatten_to_bits env) vs in
    let poutvs = List.fold_right (fun v1 v2 -> EcCoreLib.CI_List.p_cons @@! [v1; v2]) poutvs (fop_empty (List.hd poutvs).f_ty) in
    let poutvs = EcCoreLib.CI_List.p_flatten @@! [poutvs] in
    let poutvs = EcCoreLib.CI_List.p_chunk   @@! [f_int (BI.of_int m); poutvs] in
    let poutvs = EcCoreLib.CI_List.p_map @@! [(reconstruct_from_bits_op env ty); poutvs] in
    poutvs

(* 
  Input: - form representing a list
         - path for an operator of type int -> int representing a permutation
  Output: form representing permuted list 
   *)
let permute_list (env: env) (perm: EcPath.path) (xs: form) : form = 
    let (@@!) pth args = 
      try
        EcTypesafeFol.f_app_safe env pth args 
      with EcUnify.UnificationFailure _ ->
        let err = Format.sprintf "Type mismatch in pre-post generation, check your lane and precondition types@." in
        raise (BDepError err)
    in   
    let i = (create "i", GTty tint) in
    let bty = tfrom_tlist xs.f_ty in
    EcCoreLib.CI_List.p_mkseq @@! [
      f_lambda [i] 
        (EcCoreLib.CI_List.p_nth @@! [f_op EcCoreLib.CI_Witness.p_witness [bty] bty; xs; 
          perm @@! [f_local (fst i) tint]]);
      EcCoreLib.CI_List.p_size @@! [xs]
    ]

(* FIXME: Add size checks for input and output *)
let process_bdep (bdinfo: bdep_info) (tc: tcenv1) =
  let { n; invs; inpvs; m; outvs; lane; pcond; perm; debug } = bdinfo in

  let env = FApi.tc1_env tc in
  let hyps = FApi.tc1_hyps tc in
  let pe = FApi.tc1_penv tc in
  let ppe = EcPrinting.PPEnv.ofenv env in

  let (@@!) pth args = 
    try
      EcTypesafeFol.f_app_safe env pth args 
    with EcUnify.UnificationFailure _ ->
      let err = Format.sprintf "Type mismatch in pre-post generation, check your lane and precondition types@." in
      (* raise (BDepError err) *)
      tc_error pe "%s" err
  in

  (* FIXME: lookup is done twice here, should be easy to remove *)
  let fperm_of_perm_op (perm: psymbol) : int -> int =
    let pperm, bperm = EcEnv.Op.lookup ([], perm.pl_desc) env in
    match bperm.op_kind with
    | OB_oper (Some (OP_Plain 
      {f_node = Fquant (Llambda, bnd::[], 
        {f_node = Fapp ({f_node = Fop (pth, tys)}, [dfl; lst; idx])})})) when pth = EcCoreLib.CI_List.p_nth ->
        if debug then Format.eprintf "[W] Taking the fast path for the permutation@.";
        let elems = EcCoreFol.destr_list lst |> List.map (int_of_form hyps) |> List.map (BI.to_int) |> Array.of_list in
        let idx_call = fun i -> (EcTypesafeFol.fapply_safe hyps (f_quant Llambda (bnd::[]) idx) ((f_int (BI.of_int i))::[])) |> int_of_form hyps |> BI.to_int in  
        let dfl = int_of_form hyps dfl |> BI.to_int in
        fun i -> begin
          try 
            elems.(idx_call i) 
          with Invalid_argument _ ->
            dfl
        end
    | _ -> 
      if debug then Format.eprintf "[W] Taking the slow path for the permutation (op: %a)@." EcPrinting.(pp_opdecl (PPEnv.ofenv env)) (pperm, bperm);
      (fun i ->
      let arg = f_int (BI.of_int i) in
      let call = EcTypesafeFol.f_app_safe env pperm [arg] in
      let res = EcCallbyValue.norm_cbv (EcReduction.full_red) (FApi.tc1_hyps tc) call in
      begin try
        destr_int res |> BI.to_int
      with DestrError _ ->
        tc_error pe "Application of function %s failed" (EcPath.tostring pperm)
      end
    )
  in

  let fperm, pperm = match perm with 
  | None -> None, None
  | Some perm -> 
    let pperm = EcEnv.Op.lookup ([], perm.pl_desc) env |> fst in
    let fperm = fperm_of_perm_op perm in
(*
    let fperm (i: int) = 
      let arg = f_int (BI.of_int i) in
      let call = EcTypesafeFol.f_app_safe env pperm [arg] in
      let res = EcCallbyValue.norm_cbv (EcReduction.full_red) (FApi.tc1_hyps tc) call in
      begin try
        destr_int res |> BI.to_int
      with DestrError _ ->
        tc_error pe "Application of function %s failed" (EcPath.tostring pperm)
      end
    in
*)
    Some fperm, Some pperm
  in

  (* DEBUG SECTION *)
  (* let pp_type (fmt: Format.formatter) (ty: ty) = *)
  (*   Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in *)
  
  let plane, olane = EcEnv.Op.lookup ([], lane.pl_desc) env in
  let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
  (* FIXME: Add a check that this does not return a function type 
     aka lane function only have one argument *)
  let inpbty, outbty = tfrom_tfun2 olane.op_ty in
  
  (* Refactor this *)
  
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in


  (* ------------------------------------------------------------------ *)
  let outvs = try
    get_vars env outvs hr.hs_m 
    with BDepError err ->
      tc_error pe "get_vars (outvs) error: %s" err
  in

  let out_size = List.sum (List.map 
    (function 
    | v, None -> width_of_type env (v.v_type)
    | v, Some (t, _) -> 
    let t = match v.v_type.ty_node with
    | Tconstr (_, [bsty]) -> tconstr (EcEnv.Ty.lookup_path t env) [bsty]
    | _ -> tc_error pe "Failed to parse output type %a" EcPrinting.(pp_type ppe) v.v_type
    in width_of_type env t ) 
  outvs) 
  in 

  if (out_size mod m <> 0) then tc_error pe "Output size (%d) not divisible by lane size (%d)" out_size m;
  let out_block_nr = out_size / m in
  let out_block_nr = match fperm with 
    | None -> out_block_nr
    | Some fperm -> List.init out_block_nr (fun i -> if fperm i >= 0 then 1 else 0) |> List.sum 
  in

  let post_form_of_pv (v: variable * (qsymbol * BI.zint) option) : form =
    match v with
    | v, None -> (f_pvar (pv_loc v.v_name) v.v_type (hr.hs_m |> fst)).inv
    | {v_type} as v, Some (arr_t, offset) -> 
      let f = f_pvar (pv_loc v.v_name) v.v_type (hr.hs_m |> fst) in
      array_init_from_form env f.inv (arr_t, offset)
    in

  let poutvs = try
    blocks_from_vars env 
      (List.map post_form_of_pv outvs) outbty
    with BDepError err ->
      tc_error pe "%s" err
  in

  (* OPTIONAL PERMUTATION STEP *)
  let poutvs = try 
    Option.apply (Option.map (permute_list env) pperm) poutvs 
    with BDepError err ->
      tc_error pe "%s" err
  in
  
  
  (* ------------------------------------------------------------------ *)
  let inpvs = try 
    get_vars env inpvs hr.hs_m 
    with BDepError err ->
      tc_error pe "Error in get_vars(inpvs): %s" err
  in
  let in_size = List.sum (List.map 
  (function 
    | v, None -> width_of_type env (v.v_type)
    | v, Some (t, _) -> 
    let t = match v.v_type.ty_node with
    | Tconstr (_, [bsty]) -> tconstr (EcEnv.Ty.lookup_path t env) [bsty]
    | _ -> tc_error pe "Failed to parse input type %a" EcPrinting.(pp_type ppe) v.v_type
    in width_of_type env t) 
  inpvs) in 

  EcEnv.notify ~immediate:true env `Info "in_size : %d | block_size: %d@." in_size n;
  assert (in_size mod n = 0);
  let in_block_nr = in_size / n in
  EcEnv.notify ~immediate:true env `Info "in_block_nr: %d | out_block_nr: %d@." in_block_nr out_block_nr;
  assert (in_block_nr = out_block_nr);

  let finpvs = List.map post_form_of_pv inpvs in

  let inpvs = List.map 
    (function 
    | v, None -> v, None 
    | v, Some (t, offset) -> 
        let asz, bsz = match EcEnv.Circuit.lookup_array_and_bitstring env v.v_type with
        | Some ({size = (_, Some asz)}, { size = (_, Some bsz) }) -> asz, bsz 
        | Some (_, { size = (_, None) }) -> tc_error pe "non concrete binding for input bitstring type (%a)" EcPrinting.(pp_type ppe) v.v_type
        | Some ({size = (_, None)}, _) -> tc_error pe "non concrete binding for input array type (%a)" EcPrinting.(pp_type ppe) v.v_type
        | None -> tc_error pe "Failed to lookup array or bitstring binding for input type (%a)" EcPrinting.(pp_type ppe) v.v_type
        in
        (* FIXME: Run this once to check that it is equal then remove block below *)
        let asz2 = match EcEnv.Circuit.lookup_array_path env (EcPath.fromqsymbol t) with
        | Some {size= (_, Some size)} -> size
        | Some {size= (_, None)} -> assert false
        | _ -> assert false
        in
        assert (asz = asz2);
        v, Some (bsz * asz, (BI.to_int offset) * bsz)
    ) 
  inpvs 
  in

  let outvs = List.map 
    (function 
    | v, None -> v, None 
    | v, Some (t, offset) -> 
        let asz, bsz = match EcEnv.Circuit.lookup_array_and_bitstring env v.v_type with
        | Some ({size = (_, Some asz)}, { size = (_, Some bsz) }) -> asz, bsz 
        | Some (_, { size = (_, None) }) -> tc_error pe "non concrete binding for output bitstring type (%a)" EcPrinting.(pp_type ppe) v.v_type
        | Some ({size = (_, None)}, _) -> tc_error pe "non concrete binding for output array type (%a)" EcPrinting.(pp_type ppe) v.v_type
        | None -> tc_error pe "Failed to lookup array or bitstring binding for output type (%a)" EcPrinting.(pp_type ppe) v.v_type
        in
        (* FIXME: Run this once to check that it is equal then remove block below *)
        let asz2 = match EcEnv.Circuit.lookup_array_path env (EcPath.fromqsymbol t) with
        | Some {size= (_, Some size)} -> size
        | Some {size= (_, None)} -> assert false
        | _ -> assert false
        in
        assert (asz = asz2);
        v, Some (bsz * asz, (BI.to_int offset) * bsz)
    ) 
  outvs 
  in


  let invs =
    let lookup (x : bdepvar) : ((ident * ty) * (qsymbol * BI.zint) option) list =
      let get1 (v : symbol) =
        EcEnv.Var.lookup_local v env 
      in
      match x with
      | `Var x ->
          [get1 (unloc x), None]
      | `VarRange (x, n) ->
          List.init n (fun i -> get1 (Format.sprintf "%s_%d" (unloc x) i), None) 
      | `Slice (x, (arr_t, offset)) -> 
          [get1 (unloc x), Some (unloc arr_t, offset)]
    in 
    List.map lookup invs |> List.flatten in
  (* FIXME: Why was this needed? Check that all input types were equal? *)
  (* let inty = match List.collapse inv_tys with
  | Some ty -> ty
  | None -> 
      let err = Format.sprintf "Failed to coallesce types for input@." 
      (* in raise (BDepError err) *)
      in tc_error pe "%s@." err
  in *)

  let post_form_of_lv (v: ((ident * ty) * ((qsymbol * BI.zint) option))) = 
    match v with
    | (id, ty), None -> f_local id ty
    | (id, ty), Some (arr_t, offset) -> 
      let f = f_local id ty in
      array_init_from_form env f (arr_t, offset)
  in

  let finvs = List.map post_form_of_lv invs in
  let pinvs = try
    blocks_from_vars env finvs inpbty
    with BDepError err -> 
      tc_error pe "Error while generating input variable expression for precondition:@.%s@." err
  in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [(f_op plane [] olane.op_ty); pinvs] in
  (* ------------------------------------------------------------------ *)
  let post = f_eq pinvs_post poutvs in
  let pre = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinvs] in

  if (List.compare_lengths inpvs invs <> 0) 
    then tc_error pe "Logical variables should correspond 1-1 to program variables";
  let pre = f_ands (pre::(List.map2 (fun iv ipv -> f_eq iv ipv) finvs finpvs)) in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_hoareS_conseq_nm {inv=pre; m=(fst hr.hs_m)} {inv=post; m=(fst hr.hs_m)} tc in (* FIXME: check memory here*)
  FApi.t_last (t_bdep ~debug n m inpvs outvs pcond lane fperm) tc 



let t_bdepeq (inpvs_l, inpvs_r: (variable list * variable list)) (n: int) (out_blocks: (int * variable list * variable list) list) (pcond: form option) (preprocess: bool) (tc : tcenv1) =
  (* Run bdep and check that is works FIXME *)
  let () = match (FApi.tc1_goal tc).f_node with
  | FequivS sE -> begin try List.iter (fun (m, outvs_l, outvs_r) ->
    prog_equiv_prod (FApi.tc1_hyps tc) (sE.es_ml, sE.es_mr) (sE.es_sl, sE.es_sr) (inpvs_l, inpvs_r, n) (outvs_l, outvs_r, m) pcond preprocess) out_blocks
    with BDepError err ->
      tc_error (FApi.tc1_penv tc) "Program equivalence failed with error: @.%s@." err
    end
  (* FIXME PR: Do we throw a decent error here or should this be guarded before the call? *)
  | FequivF sE -> assert false
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
  let pe = FApi.tc1_penv tc in

  (* DEBUG SECTION *)
    
  let eqS = EcLowPhlGoal.tc1_as_equivS tc in
  let mem_l, mem_r = eqS.es_ml, eqS.es_mr in

  (* ------------------------------------------------------------------ *)
  let process_block (outvsl: bdepvar list) (outvsr: bdepvar list) = 
    try 
      let outvsl = get_vars env outvsl mem_l |> List.fst in
      let poutvsl = List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_l)).inv) outvsl in

      let outvsr = get_vars env outvsr mem_r |> List.fst in
      let poutvsr = List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_r)).inv) outvsr in
      List.map2 f_eq poutvsl poutvsr |> f_ands, (outvsl, outvsr)
    with BDepError err -> 
      tc_error pe "Process block failed with error: %s@." err
  in
   

  let inpvsl = try 
    get_vars env inpvsl mem_l |> List.fst 
    with BDepError err ->
      tc_error pe "%s" err
  in
  let pinpvsl = try 
    List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_l)).inv) inpvsl 
    with BDepError err ->
      tc_error pe "%s" err
  in

  let inpvsr = try 
    get_vars env inpvsr mem_r |> List.fst
    with BDepError err ->
      tc_error pe "%s" err
  in
  let pinpvsr = try 
    List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst mem_r)).inv) inpvsr 
    with BDepError err ->
      tc_error pe "%s" err
  in

  let pre = List.map2 f_eq pinpvsl pinpvsr |> f_ands in
  let post, outvs = List.map (fun (m, vs_l, vs_r) -> 
    let post, outvs = process_block vs_l vs_r in 
    let outvs_l, outvs_r = outvs in
    post, (m, outvs_l, outvs_r)) bdeinfo.out_blocks |> List.split in
  let post = f_ands post in
  
  
  let prepcond, pcond = match bdeinfo.pcond with
    | Some pcond -> 
      (* FIXME: generate correct precond. Is this fixed ? *) 
      let ppcond, opcond = EcEnv.Op.lookup ([], pcond.pl_desc) env in
      let pcond = match opcond.op_kind with
        | OB_oper (Some OP_Plain f) -> f
        | _ -> tc_error pe "Unsupported precondition kind for bdepeq"
      in

      let opinty = 
        match opcond.op_ty.ty_node with
      | Tfun (a, b) -> a
      | _ -> tc_error pe "precond should have function type"
      in
      
      let pinpl_blocks = try
        blocks_from_vars env pinpvsl opinty
        with BDepError err ->
          tc_error pe "%s" err
      in

      let pre_l = EcCoreLib.CI_List.p_all @@! [(f_op ppcond [] opcond.op_ty); pinpl_blocks] in

      pre_l, Some pcond
    | None -> f_true, None
  in

  let pre = f_and pre prepcond in
  
  (* ------------------------------------------------------------------ *)
  let tc = EcPhlConseq.t_equivS_conseq_nm {inv=pre; mr=(fst mem_r); ml=(fst mem_l)} {inv=post; mr=(fst mem_r); ml=(fst mem_l)} tc in (* FIXME: check memory *)
  FApi.t_last (t_bdepeq (inpvsl, inpvsr) n outvs pcond preprocess) tc 

let t_bdep_form 
  (invs: variable list)
  (f: form)
  (v: variable)
  (tc : tcenv1)
  : tcenv =
  match (FApi.tc1_goal tc).f_node with
  | FhoareS sF ->
    if circ_form_eval_plus_equiv ~mem:(fst sF.hs_m) (FApi.tc1_hyps tc) sF.hs_s invs f v then
      FApi.t_last (fun tc -> FApi.close (!@ tc) VBdep) (EcPhlConseq.t_hoareS_conseq_nm (hs_pr sF) {(hs_po sF) with inv=(f_and f sF.hs_po)} tc)
    else tc_error (FApi.tc1_penv tc) "Supplied formula is not always true@."
  | _ -> tc_error (FApi.tc1_penv tc) "Goal should be a Hoare judgement with inlined code@."

let process_bdep_form 
  (invs: bdepvar list)
  (f: pformula)
  (v: bdepvar)
  (tc : tcenv1)
  : tcenv =
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in
  let hyps = FApi.tc1_hyps tc in
  let env = toenv hyps in
  let invs = get_vars env invs hr.hs_m |> List.fst in
  let v = get_var env v hr.hs_m |> List.fst |> as_seq1 in
  let ue = EcUnify.UniEnv.create None in
  let env = (toenv hyps) in
  let env = Memory.push_active_ss hr.hs_m env in
  let f = EcTyping.trans_prop env ue f in
  assert (EcUnify.UniEnv.closed ue);
  let f = EcCoreSubst.Fsubst.f_subst (Tuni.subst (EcUnify.UniEnv.close ue)) f in
  t_bdep_form invs f v tc

(* FIXME: move? V *)
let form_list_from_iota (hyps: hyps) (f: form) : form list =
  match f.f_node with
  | Fapp ({f_node = Fop(p, _)}, [n; m]) when p = EcCoreLib.CI_List.p_iota ->
    let n = int_of_form hyps n in
    let m = int_of_form hyps m in
    List.init (BI.to_int m) (fun i -> f_int (BI.(add n (of_int i))))
  | _ -> let err = Format.asprintf "Failed to get form list from iota expression %a@."
    (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (toenv hyps))) f in
    raise (BDepError err)

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
      if debug then Option.may (fun ppenv -> Format.eprintf "Failed to destructure claimed list: %a@." (EcPrinting.pp_form ppenv) f) ppenv;
      raise (CircError "Failed to destruct list")

(* FIXME: move? A *)

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
  | FhoareS sF -> begin try mapreduce_eval (FApi.tc1_hyps tc) sF.hs_m sF.hs_s (inpvs, n) (outvs, m) op range sign with
    | BDepError err -> tc_error (FApi.tc1_penv tc) "Error in bdep eval: %s@." err
    end
  (* FIXME PR: Do we throw a decent error here or should this be guarded before the call? *)
  | FhoareF sH -> assert false  
  | FbdHoareF _ -> assert false
  | FbdHoareS _ -> assert false 
  | FeHoareF _ -> assert false
  | FeHoareS _ -> assert false 
  | _ -> assert false
  in
  FApi.close (!@ tc) VBdep

let process_bdep_eval (bdeinfo: bdep_eval_info) (tc: tcenv1) =
  let { in_ty; out_ty; invs; inpvs; outvs; lane; range; sign } = bdeinfo in

  (* ------------------------------------------------------------------ *)
  let env = FApi.tc1_env tc in
  let hr = EcLowPhlGoal.tc1_as_hoareS tc in
  let hyps = FApi.tc1_hyps tc in
  let ppenv = EcPrinting.PPEnv.ofenv env in
  let pe = FApi.tc1_penv tc in

  (* ------------------------------------------------------------------ *)
  let (@@!) pth args = 
    try
      EcTypesafeFol.f_app_safe env pth args 
    with EcUnify.UnificationFailure _ ->
      tc_error pe
        "Type mismatch in pre-post generation, check your lane and precondition types@.\
        Args: %a@." 
        (fun fmt fs -> List.iter 
          (fun f -> (Format.fprintf fmt "%a | "(EcPrinting.pp_form ppenv) f))
          fs) 
        args 
  in
  (* ------------------------------------------------------------------ *)
  let (@@!!) pth args = 
    try
      EcTypesafeFol.f_app_safe ~full:false env pth args 
    with EcUnify.UnificationFailure _ ->
      tc_error (FApi.tc1_penv tc) "Type mismatch in pre-post generation, check your lane and precondition types@." 
  in

  (* DEBUG SECTION *)
  (* ------------------------------------------------------------------ *)
  let pp_type (fmt: Format.formatter) (ty: ty) =
    Format.fprintf fmt "%a" (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) ty in
  
  (* ------------------------------------------------------------------ *)
  let plane, olane = EcEnv.Op.lookup ([], lane.pl_desc) env in

  (* ------------------------------------------------------------------ *)
  let in_ty =
    let ue = EcUnify.UniEnv.create None in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue in_ty in
    assert (EcUnify.UniEnv.closed ue);
    ty_subst (Tuni.subst (EcUnify.UniEnv.close ue)) ty 
  in

  (* ------------------------------------------------------------------ *)
  let out_ty =
    let ue = EcUnify.UniEnv.create None in
    let ty = EcTyping.transty EcTyping.tp_tydecl env ue out_ty in
    assert (EcUnify.UniEnv.closed ue);
    ty_subst (Tuni.subst (EcUnify.UniEnv.close ue)) ty 
  in

  (* ------------------------------------------------------------------ *)
  let ue = EcUnify.UniEnv.create None in
  let env = Memory.push_active_ss hr.hs_m env in

  (* ------------------------------------------------------------------ *)
  let range = EcTyping.trans_form env ue range (tconstr EcCoreLib.CI_List.p_list [tint])in
  assert (EcUnify.UniEnv.closed ue);
  let range = EcCoreSubst.Fsubst.f_subst (Tuni.subst (EcUnify.UniEnv.close ue)) range in

  let frange = try form_list_from_iota hyps range 
    with BDepError err -> tc_error pe "%s" err
  in


  (* ------------------------------------------------------------------ *)
  let n, in_to_uint, in_to_sint,in_of_int = 
    match EcEnv.Circuit.lookup_bitstring env in_ty with
    | Some {size = (_, Some size); touint; tosint; ofint} -> size, touint, tosint, ofint
    | Some {size = (_, None); _} -> raise (BDepError "No concrete binding for input")
    | _ -> tc_error pe "No binding for type %a@." pp_type in_ty 
  in

  let in_to_uint = f_op in_to_uint [] (tfun in_ty tint) in
  let in_to_sint = f_op in_to_sint [] (tfun in_ty tint) in
  let in_of_int = f_op in_of_int [] (tfun tint in_ty) in

  (* ------------------------------------------------------------------ *)
  let m, out_of_int = match EcEnv.Circuit.lookup_bitstring env out_ty with
  | Some {size = (_, Some size); ofint} -> size, ofint 
  | Some {size = (_, None); _} -> raise (BDepError "No concrete binding for output") 
  | _ -> tc_error pe "No binding for type %a@." pp_type out_ty 
  in
  let out_of_int = f_op out_of_int [] (tfun tint out_ty) in
  
  (* ------------------------------------------------------------------ *)
  let outvs  = get_vars env outvs hr.hs_m |> List.fst in
  let poutvs = List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)).inv) outvs in
  let poutvs = blocks_from_vars env poutvs out_ty in
  
  (* ------------------------------------------------------------------ *)
  let inpvs = get_vars env inpvs hr.hs_m |> List.fst in
  let finpvs = List.map (fun v -> (EcFol.f_pvar (pv_loc v.v_name) v.v_type (fst hr.hs_m)).inv) inpvs in
  let invs, inv_tys =
    let lookup (x : bdepvar) : (ident * ty) list =
      let get1 (v : symbol) =
        EcEnv.Var.lookup_local v env 
      in
      match x with
      | `Var x ->
          [get1 (unloc x)]
      | `VarRange (x, n) ->
          List.init n (fun i -> get1 (Format.sprintf "%s_%d" (unloc x) i)) 
      | `Slice _ -> tc_error pe "Input slice not currently supported" (* FIXME PR: Do we want to implement this ? *) 

    in List.map lookup invs |> List.flatten |> List.split in

  let inty = match List.collapse inv_tys with
  | Some ty -> ty
  | None -> tc_error pe "Failed to coallesce types for input@." 
  in
  let finvs = List.map (fun id -> f_local id inty) invs in
  let pinvs = blocks_from_vars env finvs in_ty in
  let pinvs_post = if sign 
    then EcCoreLib.CI_List.p_map @@! [in_to_sint; pinvs] 
    else EcCoreLib.CI_List.p_map @@! [in_to_uint; pinvs] 
  in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [(f_op plane [] olane.op_ty); pinvs_post] in
  let pinvs_post = EcCoreLib.CI_List.p_map @@! [out_of_int; pinvs_post] in

  (* ------------------------------------------------------------------ *)
  let post = f_eq pinvs_post poutvs in
  let pre = EcCoreLib.CI_List.p_all @@! 
    [(EcCoreLib.CI_List.p_mem @@!! [
      (EcCoreLib.CI_List.p_map @@! [in_of_int; range])]); pinvs] in

  assert (List.compare_lengths inpvs invs = 0);
  let pre = f_ands (pre::(List.map2 (fun iv ipv -> f_eq iv ipv) finvs finpvs)) in

  (* let env, hyps, concl = FApi.tc1_eflat tc in *)
  let tc = EcPhlConseq.t_hoareS_conseq_nm {inv=pre; m=(fst hr.hs_m)} {inv=post; m=(fst hr.hs_m)} tc in
  FApi.t_last (t_bdep_eval n m inpvs outvs lane frange sign) tc 

(* Should return a list of circuits corresponding to the atomic parts of the pre *)
(* 
  This means: 
  /\ p_i => [p_i]_i, 
  a = b  => [a.[i] = b.[i]]_i 
*)
(* Returns _open_ circuits *)
let process_pre (tc: tcenv1) (m: memenv) (f: form) : state * circuit list = 
  let debug = false in
  let env = FApi.tc1_env tc in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let hyps = FApi.tc1_hyps tc in (* FIXME: should target be specified here? *)

  (* Maybe move this to be a parameter and just supply it from outside *)
  let st = circuit_state_of_hyps hyps in

  (* Takes in a form of the form /\_i f_i 
     and returns a list of the conjunction terms [ f_i ]*)
  let rec destr_conj (f: form) : form list = 
    let f = (EcCallbyValue.norm_cbv (circ_red hyps) hyps f) in
    match f.f_node with
    | Fapp ({f_node = Fop (p, _)}, fs) -> begin match (EcFol.op_kind p, fs) with
      | Some (`And _), _ -> List.flatten @@ List.map destr_conj fs
      | (None, [f;fs]) when p = EcCoreLib.CI_List.p_all -> 
        let fs = form_list_from_iota hyps fs in
        List.map (fun farg -> f_app f (farg::[]) tbool) fs
      | _ -> f::[]
    end
    | _ -> f::[]
  in

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
      | Some `Eq, {f_node = Fpvar (PVloc pv, m_); _}, ({f_node = Flocal id; f_ty; _} as fv)
      | Some `Eq, ({f_node = Flocal id; f_ty; _} as fv), {f_node = Fpvar (PVloc pv, m_); _} when fst m = m_ -> 
        if debug then Format.eprintf "Adding equality to known information for translation: %a@." EcPrinting.(pp_form PPEnv.(ofenv env)) f;
        update_state_pv s m_ pv (circuit_of_form ~st hyps fv |> snd)
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
      let hyps, c1 = circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f1) in
      let hyps, c2 = circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f2) in
      circuit_eqs c1 c2
    | _ -> 
      begin
      if debug then
      Format.eprintf "Processing form: %a@.Simplified version: %a@."
        EcPrinting.(pp_form ppe) f
        EcPrinting.(pp_form ppe) (EcCallbyValue.norm_cbv (circ_red hyps) hyps f);
      try (circuit_of_form ~st hyps (EcCallbyValue.norm_cbv (circ_red hyps) hyps f) |> snd)::[] with
      e -> begin if debug then Format.eprintf "Encountered exception when converting part of the pre to circuit: %s@." (Printexc.to_string e);
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
  let time (env: env) (t: float) (msg: string) : float =
    let new_t = Unix.gettimeofday () in
    EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. t);
    new_t
  in

  let tm = Unix.gettimeofday () in
  let env = toenv hyps in

  if debug then Format.eprintf "Solving post: %a@." 
  EcPrinting.(pp_form PPEnv.(ofenv (toenv hyps))) post;
  match post.f_node with
  | Fapp ({f_node= Fop(p, _); _}, [f1; f2]) -> begin match EcFol.op_kind p with
    | Some `Eq -> if debug then Format.eprintf "Filletting circuit...@.";
      let c1 = circuit_of_form ~st hyps f1 |> snd |> state_close_circuit st in
      let c2 = circuit_of_form ~st hyps f2 |> snd |> state_close_circuit st in

      let pres = List.map (state_close_circuit st) pres in (* Assumes pres come open *)
      assert (Option.is_none @@ circuit_has_uninitialized c1);
      assert (Option.is_none @@ circuit_has_uninitialized c2);
      let posts = circuit_eqs c1 c2 in
      let tm = time env tm "Done with postcondition circuit generation" in

(*
      if debug then begin
        Format.eprintf "Got conditions:@.%a@."
        EcPrinting.(pp_list "@." pp_flatcirc) 
        (List.map (fun (c, _) -> c.reg) posts)
      end;
*)

      if debug then Format.eprintf "Number of checks before batching: %d@." (List.length posts);
      let posts = batch_checks posts in
      if debug then Format.eprintf "Number of checks after batching: %d@." (List.length posts);
      let tm = time env tm "Done with lane compression" in
      if fillet_tauts pres posts then begin
        let tm = time env tm "Done with equivalence checking (structural equality + SMT)" in
        true
      end
      else begin
        let tm = time env tm "Failed equivalence check" in
        false
      end
(*
      let cs1 = fillet_circuit c1 in
      let cs2 = fillet_circuit c2 in
      List.iter2 (fun c1 c2 ->
        Format.eprintf "Proving equiv between %a @.and@. %a@."
        pp_circuit c1 pp_circuit c2) cs1 cs2;
      assert (List.for_all2 circ_equiv cs1 cs2);
      assert false
*)
    | _ -> circuit_of_form ~st hyps post |> snd |> state_close_circuit st |> circ_taut
  end
  | _ -> circuit_of_form ~st hyps post |> snd |> state_close_circuit st |> circ_taut

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
    | FhoareS {hs_m; hs_pr; hs_po; hs_s} -> 
      let tm = Unix.gettimeofday () in
      let st, cpres = process_pre tc hs_m hs_pr in
      let tm = time (toenv hyps) tm "Done with precondition processing" in

      let hyps, st = state_of_prog hyps (fst hs_m) ~st hs_s.s_node [] in
      let tm = time (toenv hyps) tm "Done with program circuit gen" in
(*       let hyps, cpost = circuit_of_form ~st hyps hs_po in *)
(*       if debug then Format.eprintf "cpost: %a@." pp_flatcirc (fst cpost).reg; *)
(*
      let cgoal = circuit_or (circuit_not cpre) cpost in
      let cgoal = state_close_circuit st cgoal in
      assert (Option.is_none @@ circuit_has_uninitialized cgoal);
*)
(*
      if debug then Format.eprintf "circuit goal: %a@." pp_circuit cgoal;
      if debug then Format.eprintf "goal: %a@." pp_flatcirc (fst cgoal).reg;
*)
      if 
(*         (circ_taut cgoal)  *)
        solve_post ~st ~pres:cpres hyps hs_po
      then FApi.close (!@ tc) VBdep else
      raise (BDepError "Failed to verify postcondition")
    | _ -> 
    let ctxt = tohyps hyps in
    assert (ctxt.h_tvar = []);
    let st = circuit_state_of_hyps hyps in
    let cgoal = (circuit_of_form ~st hyps goal |> snd |> state_close_circuit st) in
    if debug then Format.eprintf "goal: %a@." pp_flatcirc (fst cgoal).reg;
    if circ_taut cgoal then
    FApi.close (!@ tc) VBdep
    else 
    tc_error (FApi.tc1_penv tc) "Failed to solve goal through circuit reasoning@\n"  
  end
