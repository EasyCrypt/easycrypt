(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcPath
open EcEnv
open EcAst
open EcCoreFol
open EcIdent
open LDecl
open EcLowCircuits

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

(* -------------------------------------------------------------------- *)
module C_ = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.Hlaig
end


(* -------------------------------------------------------------------- *)
let debug : bool = EcLowCircuits.debug

(* -------------------------------------------------------------------- *)
let circ_red (hyps: hyps) = let base_red = EcReduction.full_red in
  {base_red with delta_p = (fun pth ->
  if (EcEnv.Circuit.reverse_operator (LDecl.toenv hyps) pth |> List.is_empty) then
    base_red.delta_p pth
  else
    `No)
} 

(* -------------------------------------------------------------------- *)
type width = int
exception CircError of string

let ctype_of_ty (env: env) (ty: ty) : ctype = 
  match ty.ty_node with
  | Ttuple tys -> `CTuple (List.map (fun t -> EcEnv.Circuit.lookup_bitstring_size env t |> Option.get) tys)
  | Tconstr (pth, []) when pth = EcCoreLib.CI_Bool.p_bool -> `CBool
  | _ -> begin
    match EcEnv.Circuit.lookup_array_and_bitstring env ty with
    | Some ({size=(_, Some size_arr)}, {size=(_, Some size_bs)}) -> `CArray (size_bs, size_arr)
    | None -> 
      begin match EcEnv.Circuit.lookup_bitstring_size env ty with
      | Some sz -> `CBitstring sz
      | _ ->
          Format.eprintf "Missing binding for type %a@." 
          EcPrinting.(pp_type (PPEnv.ofenv env)) ty;
          raise (CircError "Failed to convert EC type to Circuit type")
    end
    | Some ({size = (_, None)}, _) -> 
      raise (CircError ("No concrete binding for array type " ^ (Format.asprintf "%a" EcPrinting.(pp_type PPEnv.(ofenv env)) ty)))
    | Some (_, {size = (_, None)}) -> 
      raise (CircError ("No concrete binding for bitstring type " ^ (Format.asprintf "%a" EcPrinting.(pp_type PPEnv.(ofenv env)) ty)))
  end


let width_of_type (env: env) (t: ty) : int =
  let cty = ctype_of_ty env t in
  EcLowCircuits.size_of_ctype cty
    
(* Requires concrete bindings for both types *)
let destr_array_type (env: env) (t: ty) : (int * ty) option = 
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({size = (_, Some size)}, {type_; size = (_, Some _)}) -> Some (size, EcTypes.tconstr type_ [])
  | _ -> None

(* FIXME: Fix an order for array size parameters, this one goes against the rest *)
let shape_of_array_type (env: env) (t: ty) : (int * int) = 
    match ctype_of_ty env t with
    | `CArray (w, n) -> (n, w)
    | _ -> raise (CircError "shape_of_array_type on non array type")
    
(* Should correspond to QF_ABV *) 
module BVOps = struct
  let temp_symbol = "temp_circ_input"
  
  let is_of_int (env: env) (p: path) : bool = 
    match EcEnv.Circuit.reverse_bitstring_operator env p with
    | Some (_, `OfInt) -> true
    | _ -> false

  let op_is_parametric_bvop (env: env) (op: path) : bool =
    match EcEnv.Circuit.lookup_bvoperator_path env op with 
    | Some { kind = `ASliceGet _ } 
    | Some { kind = `ASliceSet _ } 
    | Some { kind = `Extract _ }
    | Some { kind = `Insert _ }
    | Some { kind = `Map _ } 
    | Some { kind = `Get _ } 
    | Some { kind = `AInit _ } 
    | Some { kind = `Init _ } -> true
    | _ -> false

  let circuit_of_parametric_bvop (env : env) (op: [`Path of path | `BvBind of EcDecl.crb_bvoperator]) (args: arg list) : circuit =
    let op = match op with
    | `BvBind op -> op
    | `Path p -> begin match EcEnv.Circuit.lookup_bvoperator_path env p with
      | Some op -> op
      | None -> raise (CircError ("No binding matching operator at path " ^ (EcPath.tostring p)) )
    end
    in
    circuit_of_parametric_bvop op args
    
  let op_is_bvop (env: env) (op : path) : bool =
    match EcEnv.Circuit.lookup_bvoperator_path env op with
    | Some { kind = `Add _ }      | Some { kind = `Sub _ } 
    | Some { kind = `Mul _ }      | Some { kind = `Div _ }  
    | Some { kind = `Rem _ }      | Some { kind = `Shl _ }  
    | Some { kind = `Shr _ }      | Some { kind = `Rol _ }  
    | Some { kind = `Shrs _ }     | Some { kind = `Shls _ }  
    | Some { kind = `Ror _ }      | Some { kind = `And _ }  
    | Some { kind = `Or _ }       | Some { kind = `Xor _ }  
    | Some { kind = `Not _ }      | Some { kind = `Lt _ } 
    | Some { kind = `Le _ }       | Some { kind = `Extend _ } 
    | Some { kind = `Truncate _ } | Some { kind = `Concat _ } 
    | Some { kind = `A2B _ }      | Some { kind = `B2A _ } 
    | Some { kind = `Opp _ } -> true
    | Some { kind = 
        `ASliceGet _ 
      | `ASliceSet _ 
      | `Extract _ 
      | `Insert _ 
      | `Map _ 
      | `AInit _ 
      | `Get _ 
      | `Init _  } 
    | None -> false 

  let circuit_of_bvop (env: env) (op: [`Path of path | `BvBind of EcDecl.crb_bvoperator]) : circuit = 
    let op = match op with
    | `BvBind op -> op
    | `Path p -> begin match EcEnv.Circuit.lookup_bvoperator_path env p with
      | Some op -> op
      | None -> raise (CircError ("No binding matching operator at path " ^ (EcPath.tostring p)) )      
    end
    in
    circuit_of_bvop op
end
open BVOps

module BitstringOps = struct
  type binding = crb_bitstring_operator 

  let op_is_bsop (env: env) (op: path) : bool = 
    match EcEnv.Circuit.reverse_bitstring_operator env op with
    | Some (_, `OfInt) -> true 
    | _ -> false

  let circuit_of_bsop (env: env) (op: [`Path of path | `BSBinding of binding]) (args: arg list) : circuit =
    let bnd = match op with
    | `BSBinding bnd -> bnd
    | `Path p -> begin match EcEnv.Circuit.reverse_bitstring_operator env p with
      | Some bnd -> bnd
      | None -> raise (CircError ("No binding matching operator at path " ^ (EcPath.tostring p)))
      end
    in
    (* assert false => should be guarded by a previous call to op_is_bsop *)
    match bnd with
    | bs, `From -> assert false (* doesn't translate to circuit *)
    | {size = (_, Some size)}, `OfInt -> begin match args with
      | [ `Constant i ] ->
        circuit_of_zint ~size i
      | args -> raise (CircError (Format.asprintf "Bad arguments for bitstring of_int: expected (int) got (%a)" EcPrinting.(pp_list ", " pp_arg) args))
    end
    | {size = (_, None)}, `OfInt -> 
        raise (CircError "No concrete binding for type of of_int@.") (* FIXME: error messages *)
    | bs, `To -> assert false (* doesn't translate to circuit *)
    | bs, `ToSInt -> assert false (* doesn't translate to circuit *) 
    | bs, `ToUInt -> assert false (* doesn't translate to circuit *)
end
open BitstringOps

module ArrayOps = struct
  type binding = crb_array_operator 

  
  let op_is_arrayop (env: env) (op: path) : bool = 
    match EcEnv.Circuit.reverse_array_operator env op with
    | Some (_, `Get) -> true
    | Some (_, `Set) -> true
    | Some (_, `OfList) -> true
    | _ -> false

  let circuit_of_arrayop (env: env) (op: [`Path of path | `ABinding of binding]) (args: arg list) : circuit =
    let op = match op with
    | `ABinding bnd -> bnd
    | `Path p -> begin match EcEnv.Circuit.reverse_array_operator env p with
      | Some bnd -> bnd
      | None -> raise (CircError ("No binding matching operator at path " ^ (EcPath.tostring p))) 
    end
    in
    (* assert false => should be guarded by a call to op_is_arrayop *)
    match op with
    | (arr, `ToList) -> assert false (* We do not translate this to circuit *)
    | (arr, `Get) -> begin match args with
      | [ `Circuit ((`CArray _, inps) as arr); `Constant i] ->
        array_get arr (BI.to_int i)
      | args -> 
        let err = Format.asprintf "Bad inputs to arr get: Expected (arr, idx) got (%a)" (EcPrinting.pp_list "," pp_arg) args in
        raise (CircError err)
    end
    (* FIXME: Check argument order *)
    | ({size = (_, Some size)}, `OfList) -> begin match args with 
      | [ `Circuit dfl; `List cs ] -> array_oflist cs dfl size
      | args -> 
        let err = Format.asprintf "Bad inputs to arr of_list: Expected (default, list) got (%a)" (EcPrinting.pp_list "," pp_arg) args in
        raise (CircError err)
      end
    | ({size = (_, None)}, `OfList) -> raise (CircError "Array of list with non-concrete size")
    | (_arr, `Set) -> begin match args with
      | [ `Circuit ((`CArray _, _) as arr); 
          `Constant i; 
          `Circuit ((`CBitstring _, _) as bs) ] ->
        array_set arr (BI.to_int i) bs
      | args -> 
        let err = Format.asprintf "Bad inputs to arr set: Expected (arr, idx, new_val) got (%a)" (EcPrinting.pp_list "," pp_arg) args in
        raise (CircError err)
    end
end
open ArrayOps

(* Functions for dealing with uninitialized inputs *)
let circuit_uninit (env:env) (t: ty) : circuit = 
  circuit_uninit (ctype_of_ty env t)

module CircuitSpec = struct
  let circuit_from_spec env (c : [`Path of path | `Bind of EcDecl.crb_circuit ] ) : circuit = 
    let c = match c with
    | `Path p -> begin match EcEnv.Circuit.reverse_circuit env p with
      | Some c -> c
      | None -> raise (CircError ("No spec binding for operator at path " ^ EcPath.(tostring p)))
    end
    | `Bind c -> c
    in
    let _, name = (EcPath.toqsymbol c.operator) in
    let op = EcEnv.Op.by_path c.operator env in

    let unroll_fty (ty: ty) : ty list * ty =
      let rec doit (acc: ty list) (ty: ty) : ty list * ty =
        try 
          let a, b = EcTypes.tfrom_tfun2 ty in
          (doit (a::acc) b)
        with
        | EcTypes.TyDestrError "fun" -> List.rev acc, ty 
      in doit [] ty
    in

    let arg_tys, ret_ty = unroll_fty op.op_ty in 
    let arg_tys = List.map (ctype_of_ty env) arg_tys in
    let ret_ty = ctype_of_ty env ret_ty in
    circuit_from_spec ~name (arg_tys, ret_ty) c.circuit 
    
  let op_has_spec env pth =
    Option.is_some @@ EcEnv.Circuit.reverse_circuit env pth
end
open CircuitSpec

let op_is_base (env: env) (p: path) : bool =
  op_is_bvop env p || 
  op_has_spec env p

let circuit_of_baseop (env: env) (p: path) : circuit =
  if op_is_bvop env p then 
    circuit_of_bvop env (`Path p)
  else if op_has_spec env p then
    circuit_from_spec env (`Path p)
  else 
    assert false (* Should be guarded by call to op_is_base *)

let op_is_parametric_base (env: env) (p: path) = 
  op_is_parametric_bvop env p ||
  op_is_arrayop env p ||
  op_is_bsop env p

let circuit_of_parametric_baseop (env: env) (p: path) (args: arg list) : circuit = 
  if op_is_parametric_bvop env p then
    circuit_of_parametric_bvop env (`Path p) args
  else if op_is_arrayop env p then
    circuit_of_arrayop env (`Path p) args
  else if op_is_bsop env p then
    circuit_of_bsop env (`Path p) args
  else
    assert false (* Should be guarded by call to op_is_parametric_base *)

let circuit_of_op (env: env) (p: path) : circuit = 
  let op = try
    EcEnv.Circuit.reverse_operator env p |> List.hd
  with Failure _ -> 
    raise (CircError "Failed reverse operator")
  in
  match op with
  | `Bitstring (bs, op) -> assert false (* Should be guarded by a call to op_is_base *)
  | `Array _ -> assert false  (* Should be guarded by a call to op_is_parametric_base *)
  | `BvOperator bvbnd -> circuit_of_bvop  env (`BvBind bvbnd)
  | `Circuit c -> circuit_from_spec env (`Bind c)
  
let circuit_of_op_with_args (env: env) (p: path) (args: arg list) : circuit  = 
  let op = try
    EcEnv.Circuit.reverse_operator env p |> List.hd
  with Failure _ -> 
    raise (CircError "Failed reverse operator")
  in
  match op with
  | `Bitstring bsbnd -> circuit_of_bsop env (`BSBinding bsbnd) args
  | `Array abnd -> circuit_of_arrayop env (`ABinding abnd) args 
  | `BvOperator bvbnd -> circuit_of_parametric_bvop env (`BvBind bvbnd) args 
  | `Circuit c -> assert false (* FIXME PR: Do we want to have parametric operators coming from the spec?  *) 
(* ------------------------------ *)


(* FIXME: why are all these openings required? *)

(* FIXME: move this to module? *)
let type_is_registered (env: env) (t: ty) : bool = 
  (Option.is_some (EcEnv.Circuit.lookup_array_and_bitstring env t)) ||
  (Option.is_some (EcEnv.Circuit.lookup_bitstring env t))

(* FIXME: Check if we need to reduce twice here *)
let int_of_form (hyps: hyps) (f: form) : zint = 
  let env = toenv hyps in
  let redmode = circ_red hyps in
  let f = 
    EcCallbyValue.norm_cbv redmode hyps f 
  in
  match f.f_node with 
  | Fint i -> i
  | _ -> begin 
    try destr_int @@ EcCallbyValue.norm_cbv EcReduction.full_red hyps f
    with 
      DestrError "int" 
    | DestrError "destr_int" ->
      let err = Format.asprintf "Failed to reduce form | %a | to integer"
        (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f in
      raise (CircError err)
    end


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

let form_is_iter (f: form) : bool = 
  match f.f_node with
  | Fapp ({f_node = Fop (p, _)}, _) when
    p = EcCoreLib.CI_Int.p_iter  ||
    p = EcCoreLib.CI_Int.p_fold  ||
    p = EcCoreLib.CI_Int.p_iteri -> true
  | _ -> false

(* Expands iter, fold and iteri (for integer arguments) *)
let expand_iter_form (hyps: hyps) (f: form) : form = 
  let redmode = circ_red hyps in
  let env = toenv hyps in
  let ppenv = EcPrinting.PPEnv.ofenv env in
  let (@!!) f fs = 
    EcTypesafeFol.fapply_safe ~redmode hyps f fs
  in

  let res = match f.f_node with 
  | Fapp ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iteri -> 
    let rep = int_of_form hyps rep in
    let is = List.init (BI.to_int rep) BI.of_int in
    if debug then Format.eprintf "Done generating functions!@.";
    let f = List.fold_left (fun f i -> 
      if debug then Format.eprintf "Expanding iter... Step #%d@.Form: %a@." (BI.to_int i)
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (toenv hyps))) f
      ;
      fn @!! [f_int i; f]
    ) base is in
    f
  | Fapp ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iter -> 
    let rep = int_of_form hyps rep in
    let is = List.init (BI.to_int rep) BI.of_int in
    let f = List.fold_left (fun f i -> fn @!! [f]) base is in
    f
  | Fapp ({f_node = Fop (p, _)}, [fn; base; rep]) when p = EcCoreLib.CI_Int.p_fold -> 
    let rep = int_of_form hyps rep in
    let is = List.init (BI.to_int rep) BI.of_int in
    let f = List.fold_left (fun f i -> fn @!! [f]) base is in
    f
  | _ -> raise (CircError (Format.asprintf "Failed to destructure form for iter expansion %a" EcPrinting.(pp_form ppenv) f))
  in
  if debug then Format.eprintf "Expanded iter form: @.%a@." EcPrinting.(pp_form ppenv) res;
  res

let circuit_of_form 
  ?(pstate  : pstate = empty_pstate) (* Program variable values *)
  ?(cache   : cache  = empty_cache)
   (hyps    : hyps) 
   (f_      : EcAst.form) 
  : hyps * circuit =

  let rec doit (cache: cache) (hyps: hyps) (f_: form) : hyps * circuit = 
    let env = toenv hyps in
    let redmode = circ_red hyps in
    (* let redmode = {redmode with delta_p = fun _ -> `No} in *)
    let fapply_safe f fs = 
      let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
      res
    in
(*
    if debug then Format.eprintf "Translating form : %a (is iter form: %s)@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f_
    (if form_is_iter f_ then "yes" else "no")
    ;
*)

    let int_of_form (f: form) : zint = 
      int_of_form hyps f
    in

    (* Supposed to be called on an apply *)
    let propagate_integer_arguments (op: form) (args: form list) : form =
      let op = 
        let pth, _ = destr_op op in
        match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
          f
        | _ -> 
          if debug then Format.eprintf "Failed to get body for op: %a\n" 
          (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) op;
          raise (CircError "Failed to get body for op in propagate integer arg")
      in
(*
      if debug then Format.eprintf "Propagating arguments for op: %a@\n" 
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) op;
*)
      let res = fapply_safe op args in 
(*
      if debug then Format.eprintf "Result: %a" 
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) res;
*)
      res
      (*
      let process_arg (arg: form) : form * (ident option) =
        match arg.f_ty with
        | t when t.ty_node = EcTypes.tint.ty_node ->
          f_int (int_of_form arg), None
        | t -> let id = create "temp" in
          f_local id t, Some id
      in
      let apply_args = List.map process_arg args in
      let new_binds = List.filter_map (function 
        | (f, Some id) -> Some (id, GTty f.f_ty) 
        | _ -> None
      ) apply_args in 
      let body = fapply_safe op (List.fst apply_args) in
      f_app (f_quant Llambda new_binds body) (List.filter (fun arg -> Option.is_some (snd (process_arg arg))) args) ret_ty
      *)
    in

    let arg_of_form (hyps: hyps) (f: form) : hyps * arg = 
      match f.f_ty with
      (* FIXME: check this *)
      | t when t.ty_node = EcTypes.tint.ty_node -> hyps, arg_of_zint (int_of_form f)
      | t when type_is_registered (LDecl.toenv hyps) t -> 
          let hyps, f = doit cache hyps f in 
          hyps, arg_of_circuit f
      | {ty_node = Tfun(i_t, c_t)} when 
          i_t.ty_node = EcTypes.tint.ty_node &&
          type_is_registered (LDecl.toenv hyps) c_t ->
          hyps, arg_of_init (fun i -> snd @@ doit cache hyps (fapply_safe f [f_int (BI.of_int i)]))
      | {ty_node = Tconstr(p, [t])} when 
          p = EcCoreLib.CI_List.p_list &&
          type_is_registered (LDecl.toenv hyps) t ->
          let hyps, cs = List.fold_left_map (fun hyps f ->
            doit cache hyps f) hyps 
            (try 
              (form_list_of_form ~ppenv:(EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)) f)
            with 
              CircError _ -> 
                raise (CircError 
                  (Format.asprintf "Failed to destructure %a as list when attempting to convert it to an argument" 
                  EcPrinting.(pp_form PPEnv.(ofenv env)) f)))
          in
          hyps, arg_of_circuits cs
      | _ -> Format.eprintf "Failed to convert form to arg: %a@." EcPrinting.(pp_form (PPEnv.ofenv env)) f; 
        raise (CircError "Failed to convert arg to form")
    in

    match f_.f_node with
    | Fint z -> raise (CircError "Translation encountered unexpected integer value")

    (* Assumes no quantifier bindings/new inputs within if *)
    | Fif (c_f, t_f, f_f) -> 
        let hyps, t = doit cache hyps t_f in
        let hyps, f = doit cache hyps f_f in
        let hyps, c = doit cache hyps c_f in
        let c = cbool_of_circuit c in
        hyps, circuit_ite ~c ~t ~f

    | Flocal idn -> 
        hyps, cache_get cache idn
    | Fop (pth, _) -> 
      begin
      if pth = EcCoreLib.CI_Witness.p_witness then 
          (if debug then Format.eprintf "Assigning witness to var of type %a@." 
          EcPrinting.(pp_type (PPEnv.ofenv env)) f_.f_ty;
          hyps, circuit_uninit env (f_.f_ty))
      else
      match EcEnv.Circuit.lookup_circuit_cache_opt env pth with
      | Some op -> 
        hyps, op
      | None -> 
      if op_is_base env pth then
        let circ = try 
          circuit_of_op env pth 
        with 
        | CircError e -> Format.eprintf "(%s ->)" (EcPath.tostring pth); raise (CircError e)
        in
        let hyps = EcEnv.Circuit.add_circuit_cache_hyps hyps pth circ in
        hyps, circ 
      else
        let hyps, circ = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
(*             if debug then Format.eprintf "[BDEP] Opening definition of function at path %s" (EcPath.tostring pth); *)
          doit cache hyps f
        | _ -> 
        begin match EcFol.op_kind (destr_op f_ |> fst) with
          | Some `True -> 
            hyps, (circuit_true :> circuit)
          | Some `False ->
            hyps, (circuit_false :> circuit)
          | _ -> 
            let err = Format.sprintf "Unsupported op kind%s@." (EcPath.tostring pth) in
            raise (CircError err)
        end
        in 
        let hyps = EcEnv.Circuit.add_circuit_cache_hyps hyps pth circ in
        hyps, circ
    end
    | Fapp (f, fs) -> begin try
    (* TODO: find a way to properly propagate int arguments. Done? *)
    begin match f with
      | {f_node = Fop (pth, _)} when op_is_parametric_base env pth -> 
        let hyps, args = List.fold_left_map (arg_of_form) hyps fs in 
        hyps, circuit_of_op_with_args env pth args

      (* For dealing with iter cases: *)
      | {f_node = Fop _} when form_is_iter f_ -> 
        trans_iter cache hyps f fs
      | {f_node = Fop (p, _)} when not (List.for_all (fun f -> f.f_ty.ty_node <> EcTypes.tint.ty_node) fs) ->
(*           if debug then Format.eprintf "Attempting to propagate interger arguments for op with path %s@." (EcPath.tostring p); *)
          doit cache hyps (propagate_integer_arguments f fs)
      | {f_node = Fop _} -> 
      (* Assuming correct types coming from EC *)
      (* FIXME: Add some extra info about errors when something here throws *)
      begin match EcFol.op_kind (destr_op f |> fst), fs with
        | Some `Eq, [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          hyps, (circuit_eq c1 c2 :> circuit)
        | Some `Not, [f] -> 
          let hyps, c = doit cache hyps f in
          let c = cbool_of_circuit c in
          hyps, (circuit_not c :> circuit)
        (* FIXME: Should this be here on inside the module? *)
        | Some `True, [] ->
          hyps, (circuit_true :> circuit)
        | Some `False, [] ->
          hyps, (circuit_false :> circuit)
        | Some `Imp, [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          let c1 = cbool_of_circuit ~strict:false c1 in
          let c2 = cbool_of_circuit ~strict:false c2 in
          hyps, (circuit_or (circuit_not c1) c2 :> circuit)
        | Some (`And _), [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          let c1 = cbool_of_circuit ~strict:false c1 in
          let c2 = cbool_of_circuit ~strict:false c2 in
          hyps, (circuit_and c1 c2 :> circuit)
        | Some (`Or _), [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          let c1 = cbool_of_circuit ~strict:false c1 in
          let c2 = cbool_of_circuit ~strict:false c2 in
          hyps, (circuit_or c1 c2 :> circuit)
        | Some `Iff, [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          let c1 = cbool_of_circuit ~strict:false c1 in
          let c2 = cbool_of_circuit ~strict:false c2 in
          hyps, (circuit_or (circuit_and c1 c2) (circuit_and (circuit_not c1) (circuit_not c2)) :> circuit)
(*         | Some `Not, [f] -> doit cache hyps (f_not f) *)
        | _ -> (* recurse down into definition *)
          let hyps, f_c = doit cache hyps f in
          let hyps, fcs = List.fold_left_map
            (doit cache)
            hyps fs 
          in
          hyps, circuit_compose f_c fcs
      end
      | _ -> (* recurse down into definition *)
        let hyps, f_c = doit cache hyps f in
        let hyps, fcs = List.fold_left_map
          (doit cache)
          hyps fs 
        in
        hyps, circuit_compose f_c fcs
    end
    with CircError e ->
      Format.eprintf "Call %a ->" EcPrinting.(pp_form (PPEnv.ofenv env)) f;
      raise (CircError e)
    end
      
    | Fquant (qnt, binds, f) -> 
      let binds = List.map (fun (idn, t) -> (idn, gty_as_ty t |> ctype_of_ty env)) binds in
      let cache = open_circ_lambda_cache cache binds in
      let hyps, circ = doit cache hyps f in
      begin match qnt with
      | Lforall 
      | Llambda -> hyps, close_circ_lambda binds circ 
      | Lexists -> raise (CircError "Universal/Existential quantification not supported")
      (* TODO: figure out how to handle quantifiers *)
      end
    | Fproj (f, i) ->
        let hyps, ftp = doit cache hyps f in
        let ftp = ctuple_of_circuit ~strict:true ftp in 
        hyps, (circuit_tuple_proj ftp i :> circuit)
    | Fmatch  (f, fs, ty) -> raise (CircError "Match not supported")
    | Flet    (LSymbol (id, t), v, f) -> 
      let hyps, vc = doit cache hyps v in
      let cache = update_cache cache id vc in
      doit cache hyps f
    | Flet    (LTuple vs, v, f) -> 
      let hyps, vc = doit cache hyps v in
      let comps = (circuits_of_circuit_tuple (ctuple_of_circuit ~strict:true vc) :> circuit list) in
      let cache = List.fold_left2 (fun cache (id, t) vc ->
        update_cache cache id vc)
        cache
        vs
        comps
      in doit cache hyps f
    | Fpvar   (pv, mem) -> 
      let v = match pv with
      | PVloc v -> v
      (* FIXME: Should globals be supported? *)
      | _ -> raise (CircError "Global vars not supported")
      in 
      let v = match pstate_get_opt pstate v with
      | Some v -> v
      | None -> 
          if debug then Format.eprintf "Assigning unassigned program variable %a of type %a@." EcPrinting.(pp_pv (PPEnv.ofenv env)) pv EcPrinting.(pp_type (PPEnv.ofenv env)) f_.f_ty; 
          circuit_uninit env f_.f_ty (* Allow uninitialized program variables *)
      in
      hyps, v
    | Fglob (id, mem) -> raise (CircError "glob not supported")
    | Ftuple comps -> 
      let hyps, comps = 
        List.fold_left_map (fun hyps comp -> doit cache hyps comp) hyps comps 
      in
      let comps = List.map (cbitstring_of_circuit ~strict:true) comps in
      assert (List.for_all (circuit_is_free) (comps :> circuit list));
      hyps, (circuit_tuple_of_circuits comps :> circuit)
      (*(* FIXME: Change to inps = [] if we disallow definitions/quantifiers inside tuples *)*)
    | _ -> raise (CircError "Unsupported form kind in translation")
  

  and trans_iter (cache: cache) (hyps: hyps) (f: form) (fs: form list) =
    (* FIXME: move auxiliary function out of the definitions *)
    let redmode = circ_red hyps in
    let env = toenv hyps in
    let ppenv = EcPrinting.PPEnv.ofenv env in
    let fapply_safe f fs = 
      let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
      res
    in
    match f, fs with
    | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iteri -> 
      let rep = int_of_form hyps rep in
      let fs = List.init (BI.to_int rep) (fun i ->
        fapply_safe fn [f_int (BI.of_int i)]
      ) in
      List.fold_lefti (fun (hyps, f) i fn -> 
        if debug then Format.eprintf "Translating iteri... Step #%d@." i;
        let hyps, fn = doit cache hyps fn in
        hyps, circuit_compose fn [f]
      ) (doit cache hyps base) fs
    (* FIXME PR: this is currently being implemented directly on circuits, do we want this case as well? *)
    | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iter -> assert false 
    | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_fold -> assert false 
    | _ -> raise (CircError (Format.asprintf "Failed to destr form %a to translate iter" EcPrinting.(pp_form ppenv) f))
  in 
(*
  let t0 = Unix.gettimeofday () in
  let () = if debug then Format.eprintf "Translating form %a@\n" (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f_ in
*)

  let hyps, f_c = doit cache hyps f_ in

(*
  let () = if debug then Format.eprintf "Took %.2f s to translate form : %a@." (Unix.gettimeofday () -. t0) 
  (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f_ in
*)

  hyps, f_c


let circuit_of_path (hyps: hyps) (p: path) : hyps * circuit =
  let f = EcEnv.Op.by_path p (toenv hyps) in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> raise (CircError "Invalid operator type")
  in
  circuit_of_form hyps f

let vars_of_memtype ?pstate (env: env) (mt : memtype) =
  let Lmt_concrete lmt = mt in
  List.filter_map (function 
    | { ov_name = Some name; ov_type = ty } ->
      Some { v_name = name; v_type = ty; }
    | _ -> None
  ) (Option.get lmt).lmt_decl 
  

let process_instr (hyps: hyps) (mem: memory) ~(cache: cache) ~(pstate: pstate) (inst: instr) : hyps * pstate =
  let env = toenv hyps in
(*   if debug then Format.eprintf "[W] Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst;  *)
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) -> 
(*
      if debug then Format.eprintf "Assigning form %a to var %s@\n" 
        (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) (form_of_expr mem e) v;
*)
      let hyps, c = (form_of_expr e |> circuit_of_form ~cache ~pstate hyps) in
      let pstate = update_pstate pstate v c in
      hyps, pstate
      (* if debug then Format.eprintf "[W] Took %f seconds@." (Unix.gettimeofday() -. start); *)
    | Sasgn (LvTuple (vs), {e_node = Etuple es; _}) when List.compare_lengths vs es = 0 ->
      let pstate = List.fold_left (fun (hyps, pstate) (v, e) ->
        let hyps, c = (form_of_expr e |> circuit_of_form ~cache ~pstate hyps) in
        let pstate = update_pstate pstate v c in
        hyps, pstate
      ) (hyps, pstate)
        (List.combine 
          (List.map (function 
          | (PVloc v, _ty) -> v
          | _ -> raise (CircError "Failed to parse tuple assignment")) vs) 
        es) in
      pstate
    | Sasgn (LvTuple (vs), e) ->
      let hyps, c = (form_of_expr e |> circuit_of_form ~cache ~pstate hyps) in
      let tp = (ctuple_of_circuit ~strict:true c) in
      let comps = circuits_of_circuit_tuple tp in
      let pstate = List.fold_left2 (fun pstate (pv, _ty) c -> 
        let v = match pv with
        | PVloc v -> v
        | _ -> raise (CircError "Global variables not supported")
        in
        update_pstate pstate v c 
        ) pstate vs (comps :> circuit list)
      in 
      hyps, pstate
    | _ -> 
      let err = Format.asprintf "Instruction not supported: %a@." 
      (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst in
      raise (CircError err)
  with 
  | e ->
      let bt = Printexc.get_backtrace () in
      let err = Format.asprintf "BDep failed on instr: %a@.Exception thrown: %s@.BACKTRACE: %s@.@."
        (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst
        (Printexc.to_string e)
        bt in 
      raise @@ CircError err

let instrs_equiv
   (hyps       : hyps             )
   ((mem, mt)  : memenv           )
  ?(cache      : _ = empty_cache  )
  ?(keep       : EcPV.PV.t option )
  ?(pstate     : _ = empty_pstate )
   (s1         : instr list       )
   (s2         : instr list       ) : bool
=
  let env = LDecl.toenv hyps in

  let rd, rglobs = EcPV.PV.elements (EcPV.is_read  env (s1 @ s2)) in
  let wr, wglobs = EcPV.PV.elements (EcPV.is_write env (s1 @ s2)) in

  if not (List.is_empty rglobs && List.is_empty wglobs) then
    raise (CircError "the statements should not read/write globs");

  if not (List.for_all (EcTypes.is_loc |- fst) (rd @ wr)) then
    raise (CircError "the statements should not read/write global variables");

  let inputs = List.map (fun (pv, ty) -> { v_name = EcTypes.get_loc pv; v_type = ty; }) (rd @ wr) in
  let inputs = List.map (fun {v_name; v_type} -> (create v_name, ctype_of_ty env v_type)) inputs in
  let pstate = open_circ_lambda_pstate empty_pstate inputs in

  let hyps, pstate1 = List.fold_left (fun (hyps, pstate) -> process_instr ~cache hyps mem ~pstate) (hyps, pstate) s1 in
  let hyps, pstate2 = List.fold_left (fun (hyps, pstate) -> process_instr ~cache hyps mem ~pstate) (hyps, pstate) s2 in

  let pstate1 = close_circ_lambda_pstate pstate1 inputs in 
  let pstate2 = close_circ_lambda_pstate pstate2 inputs in
  (* FIXME: what was the intended behaviour for keep? *)
  match keep with
  | Some pv -> 
    let vs = EcPV.PV.elements pv |> fst in
    let vs = List.map (function 
      | (PVloc v, ty) -> (v, ty)
      | _ -> raise (CircError "global variables not supported")
      ) vs 
    in List.for_all (fun (var, ty) -> 
      let circ1 = pstate_get_opt pstate1 var in
      let circ2 = pstate_get_opt pstate2 var in
      match circ1, circ2 with
      | None, None -> true
      | None, Some circ1
      | Some circ1, None -> false (* Variable only defined on one of the blocks (and not in the prelude) *)
      | Some circ1, Some circ2 -> circ_equiv circ1 circ2 
    ) vs
  | None -> pstate_get_all pstate |> List.for_all (fun (var, _) -> 
    let circ1 = pstate_get pstate1 var in
    let circ2 = pstate_get pstate2 var in
    circ_equiv circ1 circ2 
  )

let pstate_of_prog (hyps: hyps) (mem: memory) ?(cache: cache = empty_cache) (proc: instr list) (invs: variable list) : hyps * pstate =
  let env = LDecl.toenv hyps in
  let invs = List.map (fun {v_name; v_type} -> (create v_name, ctype_of_ty env v_type)) invs in
  let pstate = open_circ_lambda_pstate empty_pstate invs in

  let hyps, pstate = 
    List.fold_left (fun (hyps, pstate) -> process_instr hyps mem ~cache ~pstate) (hyps, pstate) proc
  in
  hyps, close_circ_lambda_pstate pstate invs

(* FIXME: refactor this function *)
let rec circ_simplify_form_bitstring_equality
  ?(pstate: pstate = empty_pstate) 
  ?(pcond: circuit option)
  (hyps: hyps) 
  (f: form)
  : form =
  let env = toenv hyps in

  let pcond = Option.map cbool_of_circuit pcond in

  let rec check (f : form) =
    match EcFol.sform_of_form f with
    | SFeq (f1, f2)
         when (Option.is_some @@ EcEnv.Circuit.lookup_bitstring env f1.f_ty)
           || (Option.is_some @@ EcEnv.Circuit.lookup_array env f1.f_ty)
      ->
      let hyps, c1 = circuit_of_form ~pstate hyps f1 in
      let hyps, c2 = circuit_of_form ~pstate hyps f2 in
      (*if debug then Format.eprintf "[W]Testing circuit equivalence for forms:*)
      (*%a@.%a@.With circuits: %s | %s@."*)
      (*(EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f1*)
      (*(EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f2*)
      (*(circuit_to_string c1)*)
      (*(circuit_to_string c2);*)
      f_bool (circ_equiv ?pcond c1 c2)
    | _ -> f_map (fun ty -> ty) check f 
  in check f


(* Mli stuff needed: *)
let compute ~(sign: bool) (c: circuit) (args: zint list) : zint = 
  match compute ~sign (cbitstring_of_circuit ~strict:true c) (List.map (fun z -> arg_of_zint z) args) with
  | Some z -> z
  | None -> raise (CircError "Failed to reduce circuit to constant in compute")

let circ_equiv ?(pcond: circuit option) c1 c2 = 
  let pcond = match pcond with
  | Some c -> let c = cbool_of_circuit ~strict:false c in
    Some c
  | None -> None
  in
  circ_equiv ?pcond c1 c2

let circ_sat = circ_sat
let circ_taut = circ_taut

let circuit_permute (bsz: int) (perm: int -> int) (c: circuit) : circuit =
  let c = match c with
  | (`CBitstring r, inps) as c -> c
  | _ -> assert false (* FIXME PR: currently only implemented for bitstring, do we want to expand this ? *)
  in
  (permute bsz perm c :> circuit)

let circuit_mapreduce ?(perm : (int -> int) option) (c: circuit) (w_in: width) (w_out: width) : circuit list = 
  let c = match c, perm with 
  | (`CBitstring _, inps) as c, None -> c
  | (`CBitstring _, inps) as c, Some perm -> permute w_out perm c
  | _ -> assert false (* FIXME PR: currently only implemented for bitstring, do we want to expand this ? *)
  in
  (decompose w_in w_out c :> circuit list)

let cache_get = cache_get
let cache_add = cache_add
let empty_cache = empty_cache 
let circuit_to_string ((circ, inps): circuit) : string = Format.asprintf "(%a => %a)" EcPrinting.(pp_list ", " pp_cinp) inps pp_circ circ
let pstate_get = pstate_get 
let pstate_get_opt = pstate_get_opt
let pstate_get_all = fun pstate -> List.snd (pstate_get_all pstate)
let circuit_ueq = (fun c1 c2 -> (circuit_eq c1 c2 :> circuit))
let circuit_aggregate = 
  circuit_aggregate
let circuit_has_uninitialized = circuit_has_uninitialized

let circuit_to_file = circuit_to_file

let circuit_aggregate_inps = 
  circuit_aggregate_inputs

let circuit_slice (c: circuit) (size: int) (offset: int) = 
  circuit_slice ~size c offset

(* FIXME: this should use ids instead of strings *)
let circuit_align_inputs = 
  align_inputs 

let circuit_flatten (c: circuit) = 
  (cbitstring_of_circuit ~strict:false c :> circuit)

(* TODO: get a better name and uniformize *)
let circuit_of_form_with_hyps ?(pstate = empty_pstate) ?(cache = empty_cache) hyps f : hyps * circuit =
  let env = toenv hyps in
  let (pstate, cache, f), bnds = List.fold_left_map (fun (pstate, cache, goal) (id, lk) ->
    if debug then Format.eprintf "Processing hyp: %s@." (id.id_symb);
    match lk with
    | EcBaseLogic.LD_mem (Lmt_concrete Some {lmt_decl=decls}) -> 
      let pstate, bnds = List.fold_left_map (fun pstate {ov_name; ov_type} -> 
        match ov_name with
        | Some v -> let id = create v in 
        open_circ_lambda_pstate pstate [(id, ctype_of_ty env ov_type)], Some (id, ctype_of_ty env ov_type)
        | None -> (pstate, None)
      ) pstate decls in
      (pstate, cache, goal), List.filter_map (fun i -> i) bnds 
    | EcBaseLogic.LD_var (t, Some f) -> 
        let cache = open_circ_lambda_cache cache [(id, ctype_of_ty env t)] in
        begin try 
          ignore (circuit_of_form ~pstate ~cache hyps f);
          (pstate, cache, (f_and goal (f_eq (f_local id t) f))), [(id, ctype_of_ty env t)]
        with _ -> (pstate, cache, f_forall [(id, GTty t)] goal), [(id, ctype_of_ty env t)] (* FIXME: do we still add to cache here? *)
        end
    | EcBaseLogic.LD_var (t, None) -> 
        (pstate, 
        open_circ_lambda_cache cache [(id, ctype_of_ty env t)],
        goal), [(id, ctype_of_ty env t)]
    | EcBaseLogic.LD_hyp f_hyp -> 
        begin try
          ignore (circuit_of_form ~pstate ~cache hyps f_hyp);
          (pstate, cache, f_imp f_hyp goal), []
        with e -> 
          if debug then Format.eprintf "Failed to convert hyp %a with error:@.%s@."
          EcPrinting.(pp_form (PPEnv.ofenv (toenv hyps))) f_hyp (Printexc.to_string e);
          (pstate, cache, goal), []
        end
      | _ -> (pstate, cache, goal), []
  ) (pstate, cache, f) (List.rev (tohyps hyps).h_local)
  in 
  let bnds = List.flatten bnds in
  if debug then Format.eprintf "Converting form %a@." EcPrinting.(pp_form (PPEnv.ofenv (toenv hyps))) f;
  let hyps, c = circuit_of_form ~pstate ~cache hyps f in
  hyps, close_circ_lambda bnds c 

(*
(* FIXME : Review *)
let circuit_state_of_hyps ?(cache = empty_cache) hyps : hyps * circuit =
  let env = toenv hyps in
  let cache, bnds = List.fold_left_map (fun (cache) (id, lk) ->
    if debug then Format.eprintf "Processing hyp: %s@." (id.id_symb);
    match lk with
    | EcBaseLogic.LD_var (t, Some f) -> 
      let cache = open_circ_lambda_cache cache [(id, ctype_of_ty env t)] in
      begin try 
        ignore (circuit_of_form ~cache hyps f); (* FIXME : Add info to translation *)
        (cache), [(id, ctype_of_ty env t)]
      with _ -> (cache), [(id, ctype_of_ty env t)] (* FIXME: do we still add to cache here? *)
      end
    | EcBaseLogic.LD_var (t, None) -> 
      (open_circ_lambda_cache cache [(id, ctype_of_ty env t)]), 
      [(id, ctype_of_ty env t)]
    | EcBaseLogic.LD_hyp f_hyp ->  (* FIXME: extract this to a pcond *)
      begin try
        ignore (circuit_of_form ~cache hyps f_hyp);
        (cache), []
      with e -> 
        if debug then Format.eprintf "Failed to convert hyp %a with error:@.%s@."
        EcPrinting.(pp_form (PPEnv.ofenv (toenv hyps))) f_hyp (Printexc.to_string e);
        (cache), []
      end
    | _ -> (cache), []
  ) cache (List.rev (tohyps hyps).h_local)
  in 
  let bnds = List.flatten bnds in


  hyps, close_circ_lambda bnds c 


*)
