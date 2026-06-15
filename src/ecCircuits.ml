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
(* Profiling helper. [stopwatch env] returns a function [lap msg] that
   reports the time elapsed since the previous lap (or since creation).
   It is a no-op unless the [Circuit:timing] flag is set (default off),
   so it can be enabled globally with [pragma Circuit:timing.]. *)
let stopwatch (env : env) : string -> unit =
  if not (EcGState.get_circuit_timing (EcEnv.gstate env)) then fun _ -> ()
  else begin
    let last = ref (Unix.gettimeofday ()) in
    fun (msg : string) ->
      let now = Unix.gettimeofday () in
      (* Emitted at [`Warning] so it shows even at the default
         (compile-mode) verbosity; gated by the [Circuit:timing] flag. *)
      EcEnv.notify ~immediate:true env `Warning "[timing] %s: %.3fs@." msg
        (now -. !last);
      last := now
  end

(* -------------------------------------------------------------------- *)
(* Take the boolean verdict of a backend query [(valid, model)], dumping
   the counter-model to the user when the query failed (i.e. [not valid],
   so the lazy model is a genuine witness). The dump is gated by the
   [Circuit:debug_smt] flag (default off), enabled with
   [pragma Circuit:debug_smt.]; being lazy, the model is only forced when
   it is going to be printed. *)
let check_with_model (env : env) ((valid, model) : bool * model Lazy.t) : bool =
  if (not valid) && EcGState.get_circuit_debug_smt (EcEnv.gstate env) then begin
    EcEnv.notify ~immediate:true env `Warning "[debug_smt] counter-model:@.";
    List.iter
      (fun (id, value) ->
        EcEnv.notify ~immediate:true env `Warning "[debug_smt]   input %d = %s@."
          id value)
      (Lazy.force model)
  end;
  valid

(* -------------------------------------------------------------------- *)
let circ_red (hyps : hyps) =
  let base_red = EcReduction.full_red in
  {
    base_red with
    delta_p =
      (fun pth ->
        if
          EcEnv.Circuit.reverse_operator (LDecl.toenv hyps) pth |> List.is_empty
        then base_red.delta_p pth
        else `No);
  }

(* -------------------------------------------------------------------- *)
type circuit_conversion_call =
  [ `Convert of form
  | `ToArg of form
  | `ExpandIter of form * form list
  | `Instr of instr
  | `Memenv of memenv ]

type circuit_error =
  | MissingTyBinding of [`Ty of ty | `Path of path]
  | AbstractTyBinding of [`Ty of ty | `Path of path]
  | MissingOpBinding of path
  | MissingOpSpec of path
  | IntConversionFailure
  | MissingOpBody of path
  | CantConvertToConstant
  | CantReadWriteGlobs
  | BadFormForArg of form
  | CantConvertToCirc of
      [ `Int
      | `Op of path
      | `Quantif of quantif
      | `Match
      | `Glob
      | `ModGlob
      | `Record
      | `Hoare
      | `Instr ]
  | PropagateError of circuit_conversion_call * circuit_error

exception CircError of circuit_error

let circ_error (err : circuit_error) = raise (CircError err)

let propagate_circ_error (call : circuit_conversion_call) (err : circuit_error)
    =
  raise (CircError (PropagateError (call, err)))

let rec pp_circ_error ppe fmt (err : circuit_error) =
  let open EcPrinting in
  match err with
  | MissingTyBinding t ->
    Format.fprintf fmt "Missing type binding for ";
    begin
      match t with
      | `Path pth -> Format.fprintf fmt "type at path %a" pp_path pth
      | `Ty ty -> Format.fprintf fmt "type %a" (pp_type ppe) ty
    end
  | AbstractTyBinding t ->
    Format.fprintf fmt "No concrete (only abstract) type binding for ";
    begin
      match t with
      | `Path pth -> Format.fprintf fmt "type at path %a" pp_path pth
      | `Ty ty -> Format.fprintf fmt "type %a" (pp_type ppe) ty
    end
  | MissingOpBinding pth ->
    Format.fprintf fmt "Missing op binding for operator at path %a" pp_path pth
  | MissingOpSpec pth ->
    Format.fprintf fmt "Missing op spec binding for operator at path %a" pp_path
      pth
  | IntConversionFailure ->
    Format.fprintf fmt "Failed to convert form to concrete integer"
  | MissingOpBody pth ->
    Format.fprintf fmt "No body for operator at path %a" pp_path pth
  | CantConvertToConstant ->
    Format.fprintf fmt
      "Failed to reduce circuit to constant after composition (while \
       attempting to compute)"
  | CantReadWriteGlobs ->
    Format.fprintf fmt
      "Cannot reason about programs which write to global variables using \
       circuits"
  | BadFormForArg f ->
    Format.fprintf fmt
      "Form %a does not match any known conversion pattern from form to \
       argument"
      (pp_form ppe) f
  | CantConvertToCirc reason ->
    Format.fprintf fmt "Failed circuit conversion due to: ";
    begin
      match reason with
      | `Int ->
        Format.fprintf fmt
          "Encountered unexpected integer (maybe you are missing a binding?)"
      | `Op pth ->
        Format.fprintf fmt
          "Don't know how to convert operator at path %a to circuit (not \
           concrete and does not match any known operator kind)"
          pp_path pth
      | `Quantif qnt ->
        Format.fprintf fmt "Encountered unexpected quantifier %s"
          (string_of_quant qnt)
      | `Match ->
        Format.fprintf fmt "Conversion of match statements not supported"
      | `Glob ->
        Format.fprintf fmt "Global variables not supported in conversion"
      | `ModGlob ->
        Format.fprintf fmt "Conversion of module globals not supported"
      | `Record -> Format.fprintf fmt "Conversion of records not supported"
      | `Hoare ->
        Format.fprintf fmt "Direct conversion of hoare statements not supported"
      | `Instr -> assert false
    end
  | PropagateError (call, e) ->
    pp_circ_error ppe fmt e;
    Format.fprintf fmt "@\nWhile attemping ";
    begin
      match call with
      | `Convert f -> Format.fprintf fmt "conversion of form %a" (pp_form ppe) f
      | `ToArg f ->
        Format.fprintf fmt "conversion to arg of form %a" (pp_form ppe) f
      | `ExpandIter (f, args) ->
        Format.fprintf fmt "expansion of iter %a(%a)" (pp_form ppe) f
          (pp_list ", " (pp_form ppe))
          args
      | `Instr inst ->
        Format.fprintf fmt "processing of instruction %a" (pp_instr ppe) inst
      | `Memenv (m, mt) ->
        Format.fprintf fmt "entering memory %a : %a" (pp_mem ppe) m
          (pp_memtype ppe) mt
    end

let rec ctype_of_ty (env : env) (ty : ty) : ctype =
  match ty.ty_node with
  | Ttuple tys -> CTuple (List.map (ctype_of_ty env) tys)
  | Tconstr (pth, []) when pth = EcCoreLib.CI_Bool.p_bool -> CBool
  | _ -> begin
    match EcEnv.Circuit.lookup_array_and_bitstring env ty with
    | Some ({size = _, Some size_arr}, {size = _, Some size_bs}) ->
      CArray {width = size_bs; count = size_arr}
    | None -> begin
      match EcEnv.Circuit.lookup_bitstring_size env ty with
      | Some sz -> CBitstring sz
      | _ -> circ_error (MissingTyBinding (`Ty ty))
    end
    | Some ({size = _, None}, _) -> circ_error (AbstractTyBinding (`Ty ty))
    | Some (_, {size = _, None}) -> circ_error (AbstractTyBinding (`Ty ty))
  end

(* Should correspond to QF_ABV *)
module BVOps = struct
  let circuit_of_parametric_bvop
      (env : env)
      (op : [`Path of path | `BvBind of EcDecl.crb_bvoperator])
      (args : arg list) : circuit =
    let op =
      match op with
      | `BvBind op -> op
      | `Path p -> begin
        match EcEnv.Circuit.lookup_bvoperator_path env p with
        | Some op -> op
        | None -> circ_error (MissingOpBinding p)
      end
    in
    circuit_of_parametric_bvop op args

  let circuit_of_bvop
      (env : env)
      (op : [`Path of path | `BvBind of EcDecl.crb_bvoperator]) : circuit =
    let op =
      match op with
      | `BvBind op -> op
      | `Path p -> begin
        match EcEnv.Circuit.lookup_bvoperator_path env p with
        | Some op -> op
        | None -> circ_error (MissingOpBinding p)
      end
    in
    circuit_of_bvop op
end

open BVOps

module BitstringOps = struct
  type binding = crb_bitstring_operator

  let circuit_of_bsop
      (env : env)
      (op : [`Path of path | `BSBinding of binding])
      (args : arg list) : circuit =
    let bnd =
      match op with
      | `BSBinding bnd -> bnd
      | `Path p -> begin
        match EcEnv.Circuit.reverse_bitstring_operator env p with
        | Some bnd -> bnd
        | None -> circ_error (MissingOpBinding p)
      end
    in
    (* [classify_paramop] only ever yields the [`OfInt] bitstring
       operator, so the other arms are unreachable here. *)
    match bnd with
    | _bs, `From -> assert false (* doesn't translate to circuit *)
    | {size = _, Some size}, `OfInt -> begin
      match args with
      | [`Constant i] -> circuit_of_zint ~size i
      | _args ->
        assert
          false (* Should be caught by EC typechecking + binding correctness *)
    end
    | {size = _, None; type_ = ty}, `OfInt ->
      circ_error (AbstractTyBinding (`Path ty))
    | _bs, `To -> assert false (* doesn't translate to circuit *)
    | _bs, `ToSInt -> assert false (* doesn't translate to circuit *)
    | _bs, `ToUInt -> assert false (* doesn't translate to circuit *)
end

open BitstringOps

module ArrayOps = struct
  type binding = crb_array_operator

  let circuit_of_arrayop
      (env : env)
      (op : [`Path of path | `ABinding of binding])
      (args : arg list) : circuit =
    let op =
      match op with
      | `ABinding bnd -> bnd
      | `Path p -> begin
        match EcEnv.Circuit.reverse_array_operator env p with
        | Some bnd -> bnd
        | None -> circ_error (MissingOpBinding p)
      end
    in
    (* [classify_paramop] only yields the [`Get]/[`Set]/[`OfList] array
       operators, so the other arms are unreachable here. *)
    match op with
    | _arr, `ToList -> assert false (* We do not translate this to circuit *)
    | _arr, `Get -> begin
      match args with
      | [`Circuit (({type_ = CArray _}, _inps) as arr); `Constant i] ->
        array_get arr (BI.to_int i)
      | _args ->
        assert
          false (* Should be caught by EC typechecking + binding correctness *)
    end
    | {size = _, Some size}, `OfList -> begin
      match args with
      | [`Circuit dfl; `List cs] -> array_oflist cs dfl size
      | _args ->
        assert
          false (* Should be caught by EC typechecking + binding correctness *)
    end
    | {size = _, None; type_ = ty}, `OfList ->
      circ_error (AbstractTyBinding (`Path ty))
    | _arr, `Set -> begin
      match args with
      | [
       `Circuit (({type_ = CArray _}, _) as arr);
       `Constant i;
       `Circuit (({type_ = CBitstring _}, _) as bs);
      ] ->
        array_set arr (BI.to_int i) bs
      | _args ->
        assert
          false (* Should be caught by EC typechecking + binding correctness *)
    end
end

open ArrayOps

(* Functions for dealing with uninitialized inputs *)
let circuit_uninit (env : env) (t : ty) : circuit =
  circuit_uninit (ctype_of_ty env t)

module CircuitSpec = struct
  let circuit_from_spec env (c : [`Path of path | `Bind of EcDecl.crb_circuit])
      : circuit =
    let c =
      match c with
      | `Path p -> begin
        match EcEnv.Circuit.reverse_circuit env p with
        | Some c -> c
        | None -> circ_error (MissingOpSpec p)
        (* Will generally never happen *)
      end
      | `Bind c -> c
    in
    let _, name = EcPath.toqsymbol c.operator in
    let op = EcEnv.Op.by_path c.operator env in

    let unroll_fty (ty : ty) : ty list * ty =
      let rec doit (acc : ty list) (ty : ty) : ty list * ty =
        try
          let a, b = EcTypes.tfrom_tfun2 ty in
          doit (a :: acc) b
        with EcTypes.TyDestrError "fun" -> List.rev acc, ty
      in
      doit [] ty
    in

    let arg_tys, ret_ty = unroll_fty op.op_ty in
    let arg_tys = List.map (ctype_of_ty env) arg_tys in
    let ret_ty = ctype_of_ty env ret_ty in
    circuit_from_spec ~name (arg_tys, ret_ty) c.circuit
end

open CircuitSpec

(* A bound bv-operator is "parametric" (applied to constant arguments,
   e.g. slice indices) or "base" (a plain bitvector operation) depending
   on its kind. *)
let bvop_is_parametric (op : EcDecl.crb_bvoperator) : bool =
  match op.kind with
  | `ASliceGet _ | `ASliceSet _ | `Extract _ | `Insert _ | `Map _ | `Get _
  | `AInit _ | `Init _ ->
    true
  | _ -> false

(* Operators that translate to a circuit when applied to NO arguments. *)
type baseop = BBvOp of EcDecl.crb_bvoperator | BSpec of EcDecl.crb_circuit

(* Operators that translate to a circuit when applied to arguments. *)
type paramop =
  | PBvOp of EcDecl.crb_bvoperator
  | PArray of crb_array_operator
  | PBs of crb_bitstring_operator

(* Classify an operator path against the circuit bindings with a SINGLE
   registry lookup, returning the bound-op data (so the translators below
   need not look it up again). [None] means the path is not a circuit
   base/parametric operator. *)
let classify_baseop (env : env) (p : path) : baseop option =
  match EcEnv.Circuit.lookup_bvoperator_path env p with
  | Some op when not (bvop_is_parametric op) -> Some (BBvOp op)
  | _ -> (
    match EcEnv.Circuit.reverse_circuit env p with
    | Some c -> Some (BSpec c)
    | None -> None)

let classify_paramop (env : env) (p : path) : paramop option =
  match EcEnv.Circuit.lookup_bvoperator_path env p with
  | Some op when bvop_is_parametric op -> Some (PBvOp op)
  | _ -> (
    match EcEnv.Circuit.reverse_array_operator env p with
    | Some abnd -> Some (PArray abnd)
    | None -> (
      match EcEnv.Circuit.reverse_bitstring_operator env p with
      | Some ((_, `OfInt) as bsbnd) -> Some (PBs bsbnd)
      | _ -> None))

let circuit_of_op (env : env) (op : baseop) : circuit =
  match op with
  | BBvOp bvbnd -> circuit_of_bvop env (`BvBind bvbnd)
  | BSpec c -> circuit_from_spec env (`Bind c)

let circuit_of_op_with_args (env : env) (op : paramop) (args : arg list) :
    circuit =
  match op with
  | PBvOp bvbnd -> circuit_of_parametric_bvop env (`BvBind bvbnd) args
  | PArray abnd -> circuit_of_arrayop env (`ABinding abnd) args
  | PBs bsbnd -> circuit_of_bsop env (`BSBinding bsbnd) args

let type_has_bindings (env : env) (t : ty) : bool =
  Option.is_some (EcEnv.Circuit.lookup_array_and_bitstring env t)
  || Option.is_some (EcEnv.Circuit.lookup_bitstring env t)

let int_of_form ?(redmode = EcReduction.full_red) (hyps : hyps) (f : form) :
    zint =
  match f.f_node with
  | Fint i -> i
  | _ -> begin
    try destr_int @@ EcCallbyValue.norm_cbv redmode hyps f
    with DestrError "int" | DestrError "destr_int" ->
      circ_error IntConversionFailure
  end

let rec form_list_of_form ?(env : env option) (f : form) : form list =
  match destr_op_app f with
  | (pc, _), [h; {f_node = Fop (p, _)}]
    when pc = EcCoreLib.CI_List.p_cons && p = EcCoreLib.CI_List.p_empty ->
    [h]
  | (pc, _), [h; t] when pc = EcCoreLib.CI_List.p_cons ->
    h :: form_list_of_form t
  | _ ->
    Option.may
      (fun env ->
        EcEnv.notify env `Debug "Failed to destructure claimed list: %a@."
          (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))
          f)
      env;
    raise (DestrError "list")

let form_is_iter (f : form) : bool =
  match f.f_node with
  | Fapp ({f_node = Fop (p, _)}, _)
    when p = EcCoreLib.CI_Int.p_iter
         || p = EcCoreLib.CI_Int.p_fold
         || p = EcCoreLib.CI_Int.p_iteri ->
    true
  | _ -> false

let circuit_of_form (st : state) (hyps : hyps) (f_ : EcAst.form) : circuit =
  let redmode = circ_red hyps in
  let env = toenv hyps in
  let ppe = EcPrinting.PPEnv.ofenv env in

  let fapply_safe (f : form) (fs : form list) =
    EcTypesafeFol.fapply_safe ~redmode hyps f fs
  in

  (* Form level cache, local to each high-level call *)
  let cache : circuit EcAlphaInvHashtbl.t = EcAlphaInvHashtbl.create hyps 700 in
  let op_cache : circuit Mp.t ref = ref Mp.empty in

  let int_of_form (f : form) : zint = int_of_form hyps f in

  (* Supposed to be called on an apply *)
  let propagate_integer_arguments (op : form) (args : form list) : form =
    let op =
      let pth, _ = destr_op op in
      match (EcEnv.Op.by_path pth env).op_kind with
      | OB_oper (Some (OP_Plain f)) -> f
      | _ -> circ_error (MissingOpBody pth)
    in
    let res = fapply_safe op args in
    res
  in

  let rec arg_of_form (st : state) (f : form) : arg =
    try
      match f.f_ty with
      | t when EcReduction.EqTest.is_int env t ->
        arg_of_zint (int_of_form f)

      | t when type_has_bindings env t ->
        let f = circuit_of_node st f in
        arg_of_circuit f

      | { ty_node = Tfun (i_t, c_t) } when
          ty_equal i_t EcTypes.tint && type_has_bindings env c_t
        ->
        arg_of_init (fun i ->
            let f = fapply_safe f [f_int (BI.of_int i)] in
            circuit_of_node st f)
      | { ty_node = Tconstr (p, [t]) } when
          EcPath.p_equal p (EcCoreLib.CI_List.p_list) && type_has_bindings env t
        ->
          let cs = List.map (circuit_of_node st) (form_list_of_form ~env f) in
          arg_of_circuits cs
  
      | _ ->
        EcLowCircuits.log st
        @@ Format.asprintf "Failed to convert form to arg: %a@."
             EcPrinting.(pp_form ppe)
             f;
        circ_error (BadFormForArg f)
    with CircError e -> propagate_circ_error (`ToArg f) e

  (* State does not get backward propagated so it is not returned *)
  and circuit_of_node (st : state) (f_ : form) : circuit =
    try
      begin
        match f_.f_node with
        | Fint _z ->
          circ_error (CantConvertToCirc `Int)

        | Flocal idn -> state_get st idn

        | Fop (pth, _) -> circuit_of_op_form st f_ pth
  
        | Fapp (f, fs) -> circuit_of_app st f_ f fs
  
        | Fquant (qnt, binds, f) ->
          let binds =
            List.map (fun (idn, t) -> idn, gty_as_ty t |> ctype_of_ty env) binds
          in
          begin
            match qnt with
            | Lforall | Llambda ->
              circ_lambda_oneshot st binds (fun st -> circuit_of_node st f)
            | Lexists ->
              circ_error (CantConvertToCirc (`Quantif qnt))
          end

        | Fif (c_f, t_f, f_f) ->
          let t = circuit_of_node st t_f in
          let f = circuit_of_node st f_f in
          let c = circuit_of_node st c_f in
          circuit_ite ~c ~t ~f

        | Fproj (f, i) ->
          let ftp = circuit_of_node st f in
          (circuit_tuple_proj ftp i :> circuit)
  
        | Fmatch (_f, _fs, _ty) ->
          circ_error (CantConvertToCirc `Match)
  
        | Flet (LSymbol (id, _t), v, f) ->
          let vc = circuit_of_node st v in
          let st = update_state st id vc in
          circuit_of_node st f

        | Flet (LTuple vs, v, f) ->
          let vc = circuit_of_node st v in
          let comps = circuits_of_circuit_tuple vc in
          let st = List.fold_left2 update_state st (List.fst vs) comps in
          circuit_of_node st f

        | Flet (LRecord _, _, _) ->
          circ_error (CantConvertToCirc `Record)

        | Fpvar (pv, mem) ->
          let v =
            match pv with
            | PVloc v -> v
            | _ -> circ_error (CantConvertToCirc `Glob)
          in
          let v =
            match state_get_pv_opt st mem v with
            | Some v -> v
            | None -> assert false (* opened up front: internal error *)
          in
          v
        | Fglob (_id, _mem) ->
          circ_error (CantConvertToCirc `ModGlob)

        | Ftuple comps ->
          let comps = List.map (circuit_of_node st) comps in
          (circuit_tuple_of_circuits comps :> circuit)

        | FhoareF _ | FhoareS _ | FbdHoareF _ | FbdHoareS _ | FeHoareF _
        | FeHoareS _ | FequivF _ | FequivS _ | FeagerF _ | Fpr _ ->
          circ_error (CantConvertToCirc `Hoare)
      end
    with CircError e -> propagate_circ_error (`Convert f_) e

  (* Translate a nullary operator [Fop pth] (the whole form is [f_]). *)
  and circuit_of_op_form (st : state) (f_ : form) (pth : path) : circuit =
    if EcPath.p_equal pth EcCoreLib.CI_Witness.p_witness then begin
      EcEnv.notify env `Debug "Assigning witness to var of type %a@."
        EcPrinting.(pp_type ppe)
        f_.f_ty;
      circuit_uninit env f_.f_ty
    end else
      match Mp.find_opt pth !op_cache with
      | Some op -> op
      | None ->
        let circ = circuit_of_op_form_real st f_ pth in
        op_cache := Mp.add pth circ !op_cache;
        circ

    and circuit_of_op_form_real (st : state) (f_ : form) (pth : path) : circuit =
      match classify_baseop env pth with
      | Some op ->
        circuit_of_op env op
      | None ->
          match (EcEnv.Op.by_path pth env).op_kind with
          | OB_oper (Some (OP_Plain f)) -> circuit_of_node st f
          | _ -> begin
            match EcFol.op_kind (destr_op f_ |> fst) with
            | Some `True -> (circuit_true :> circuit)
            | Some `False -> (circuit_false :> circuit)
            | _ -> circ_error (CantConvertToCirc (`Op (destr_op f_ |> fst)))
          end

  (* Translate an operator application whose head [f] is a (non-parametric,
     non-iter, non-integer-specialized) operator applied to [fs]: the
     logical connectives, otherwise recurse into the definition. *)
  and circuit_of_logic_app (st : state) (f : form) (fs : form list) : circuit =
    match EcFol.op_kind (destr_op f |> fst), fs with
    | Some `Eq, [f1; f2] ->
      let c1 = circuit_of_node st f1 in
      let c2 = circuit_of_node st f2 in
      (circuit_eq c1 c2 :> circuit)

    | Some `Not, [f] ->
      let c = circuit_of_node st f in
      circuit_not c

    | Some `True, [] ->
      (circuit_true :> circuit)

    | Some `False, [] ->
      (circuit_false :> circuit)

    | Some `Imp, [f1; f2] ->
      let c1 = circuit_of_node st f1 in
      let c2 = circuit_of_node st f2 in
      (circuit_or (circuit_not c1) c2 :> circuit)

    | Some (`And _), [f1; f2] ->
      let c1 = circuit_of_node st f1 in
      let c2 = circuit_of_node st f2 in
      (circuit_and c1 c2 :> circuit)

    | Some (`Or _), [f1; f2] ->
      let c1 = circuit_of_node st f1 in
      let c2 = circuit_of_node st f2 in
      (circuit_or c1 c2 :> circuit)

    | Some `Iff, [f1; f2] ->
      let c1 = circuit_of_node st f1 in
      let c2 = circuit_of_node st f2 in
      (circuit_or (circuit_and c1 c2)
         (circuit_and (circuit_not c1) (circuit_not c2))
        :> circuit)

    (* Recurse down into definition *)
    | _ ->
      let f_c = circuit_of_node st f in
      let fcs = List.map (circuit_of_node st) fs in
      circuit_compose f_c fcs

  (* Translate an application [Fapp (f, fs)] (the whole form is [f_]),
     memoized in [cache]. *)
  and circuit_of_app (st : state) (f_ : form) (f : form) (fs : form list) : circuit =
    match EcAlphaInvHashtbl.find_opt cache f_ with
    | Some circ -> circ
    | None ->
      let paramop =
        match f.f_node with
        | Fop (pth, _) -> classify_paramop env pth
        | _ -> None
      in
      let circ =
        match f, paramop with
        | _, Some op ->
          let args = List.map (arg_of_form st) fs in
          circuit_of_op_with_args env op args
        (* For dealing with iter cases: *)
        | {f_node = Fop _}, _ when form_is_iter f_ -> trans_iter st hyps f fs
        | {f_node = Fop (_p, _)}, _
          when not
                 (List.for_all
                    (fun f -> f.f_ty.ty_node <> EcTypes.tint.ty_node)
                    fs) ->
          circuit_of_node st (propagate_integer_arguments f fs)
        | {f_node = Fop _}, _ ->
          (* Assuming correct types coming from EC *)
          circuit_of_logic_app st f fs
        (* Recurse down into definition *)
        | _ ->
          let f_c = circuit_of_node st f in
          let fcs = List.map (circuit_of_node st) fs in
          circuit_compose f_c fcs
      in
      EcAlphaInvHashtbl.add cache f_ circ;
      circ

  and trans_iter (st : state) (hyps : hyps) (f : form) (fs : form list) : circuit =
    try
      let redmode = circ_red hyps in
      let fapply_safe f fs =
        let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
        res
      in
      match f, fs with
      | {f_node = Fop (p, _)}, [rep; fn; base] when p = EcCoreLib.CI_Int.p_iteri
        ->
        let rep = int_of_form rep in
        let fs =
          List.init (BI.to_int rep) (fun i ->
              fapply_safe fn [f_int (BI.of_int i)])
        in
        List.fold_lefti
          (fun f i fn ->
            EcEnv.notify env `Debug "Translating iteri... Step #%d@." i;
            let fn = circuit_of_node st fn in
            circuit_compose fn [f])
          (circuit_of_node st base) fs
      (* This is defined in terms of iteri, so it should get expanded and use the case above *)
      (* | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iter -> assert false  *)
      | {f_node = Fop (p, _)}, [fn; start_val; reps]
        when p = EcCoreLib.CI_Int.p_fold ->
        let reps = int_of_form reps |> BI.to_int in
        let fn = circuit_of_node st fn in
        let start_val = circuit_of_node st start_val in
        List.fold_left
          (fun acc f -> circuit_compose f [acc])
          start_val (List.make reps fn)
      | _ -> raise (DestrError "iter")
    with CircError e -> propagate_circ_error (`ExpandIter (f, fs)) e

  in circuit_of_node st f_

let circuit_check_posts
    ~(env : env)
    ~(pres : circuit list)
    (posts : circuit list) =
  let lap = stopwatch env in

  EcEnv.notify env `Debug "Number of checks before batching: %d@."
    (List.length posts);
  let posts = batch_checks ~mode:`BySub posts in
  EcEnv.notify env `Debug "Number of checks after batching: %d@."
    (List.length posts);
  lap "Done with lane compression";
  if fillet_tauts pres posts then begin
    lap "Done with equivalence checking (structural equality + SMT)";
    true
  end
  else begin
    lap "Failed equivalence check";
    false
  end

let circuits_of_equality ~(st : state) ~(hyps : hyps) (f1 : form) (f2 : form) :
    circuit list =
  let env = toenv hyps in
  let lap = stopwatch env in

  EcEnv.notify env `Debug "Filletting circuit...@.";
  let c1 = circuit_of_form st hyps f1 |> state_close_circuit st in
  lap "Left side circuit generation done";
  let c2 = circuit_of_form st hyps f2 |> state_close_circuit st in
  lap "Right side circuit generation done";

  assert (Option.is_none @@ circuit_has_uninitialized c1);
  assert (Option.is_none @@ circuit_has_uninitialized c2);
  let posts = circuit_eqs c1 c2 in
  lap "Done with postcondition circuit generation";
  posts

let circuit_simplify_equality
    ~(st : state)
    ~(hyps : hyps)
    ~(pres : circuit list)
    (f1 : form)
    (f2 : form) : bool =
  let posts = circuits_of_equality ~st ~hyps f1 f2 in
  circuit_check_posts ~env:(toenv hyps) ~pres posts

let process_instr (hyps : hyps) (mem : memory) ~(st : state) (inst : instr) :
    state =
  EcEnv.notify (toenv hyps) `Debug "[W] Processing : %a@."
    (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv (toenv hyps)))
    inst;
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) ->
      let c = (ss_inv_of_expr mem e).inv |> circuit_of_form st hyps in
      let st = update_state_pv st mem v c in
      st
    | Sasgn (LvTuple vs, {e_node = Etuple es; _})
      when List.compare_lengths vs es = 0 ->
      let st =
        List.fold_left
          (fun st (v, e) ->
            let c = (ss_inv_of_expr mem e).inv |> circuit_of_form st hyps in
            let st = update_state_pv st mem v c in
            st)
          st
          (List.combine
             (List.map
                (function
                  | PVloc v, _ty -> v
                  | _ -> circ_error (CantConvertToCirc `Glob))
                vs)
             es)
      in
      st
    | Sasgn (LvTuple vs, e) ->
      let tp = (ss_inv_of_expr mem e).inv |> circuit_of_form st hyps in
      let comps = circuits_of_circuit_tuple tp in
      let st =
        List.fold_left2
          (fun st (pv, _ty) c ->
            let v =
              match pv with
              | PVloc v -> v
              | _ -> circ_error (CantConvertToCirc `Glob)
            in
            update_state_pv st mem v c)
          st vs
          (comps :> circuit list)
      in
      st
    | _ -> circ_error (CantConvertToCirc `Instr)
  with CircError e -> propagate_circ_error (`Instr inst) e

let instrs_equiv
    (hyps : hyps)
    ((mem, _mt) : memenv)
    ?(keep : EcPV.PV.t option)
    (st : state)
    (s1 : instr list)
    (s2 : instr list) : bool =
  let env = LDecl.toenv hyps in

  let rd, rglobs = EcPV.PV.elements (EcPV.is_read env (s1 @ s2)) in
  let wr, wglobs = EcPV.PV.elements (EcPV.is_write env (s1 @ s2)) in

  if not (List.is_empty rglobs && List.is_empty wglobs) then
    circ_error CantReadWriteGlobs;

  if not (List.for_all (EcTypes.is_loc -| fst) (rd @ wr)) then
    circ_error CantReadWriteGlobs;

  (* Open the read/written program variables as the circuit inputs, keyed
     by their (memory, name) so that [Fpvar] reads in [process_instr]
     resolve to them. Opening them with the ident-based [open_circ_lambda]
     (under fresh idents) would leave every read unbound, collapsing all
     variables to a single uninitialized input. A variable that is both
     read and written must be opened only once. *)
  let inputs =
    List.map (fun (pv, ty) -> (EcTypes.get_loc pv, ty)) (rd @ wr)
    |> List.sort_uniq (fun (a, _) (b, _) -> String.compare a b)
    |> List.map (fun (s, ty) -> ((mem, s), ctype_of_ty env ty))
  in
  let st = open_circ_lambda_pv st inputs in

  let st1 = List.fold_left (fun st -> process_instr hyps mem ~st) st s1 in
  let st2 = List.fold_left (fun st -> process_instr hyps mem ~st) st s2 in

  let st1 = close_circ_lambda st1 in
  let st2 = close_circ_lambda st2 in
  match keep with
  | Some pv ->
    let vs = EcPV.PV.elements pv |> fst in
    let vs =
      List.map
        (function
          | PVloc v, ty -> v, ty
          | _ -> circ_error (CantConvertToCirc `Glob))
        vs
    in
    List.for_all
      (fun (var, _ty) ->
        let circ1 = state_get_pv_opt st1 mem var in
        let circ2 = state_get_pv_opt st2 mem var in
        match circ1, circ2 with
        | None, None -> true
        | None, Some _ | Some _, None ->
          false
          (* Variable only defined on one of the blocks (and not in the prelude) *)
        | Some circ1, Some circ2 -> check_with_model env (circ_equiv circ1 circ2))
      vs
  | None ->
    state_get_all_memory st mem
    |> List.for_all (fun (var, _) ->
           let circ1 = state_get_pv st1 mem var in
           let circ2 = state_get_pv st2 mem var in
           check_with_model env (circ_equiv circ1 circ2))

let state_of_prog
    ?(close = false)
    (hyps : hyps)
    (mem : memory)
    ~(st : state)
    (proc : instr list) : state =
  let st = List.fold_left (fun st -> process_instr hyps mem ~st) st proc in
  if close then close_circ_lambda st else st

let circ_simplify_form_bitstring_equality
    ?(st : state = empty_state)
    ?(pres : circuit list = [])
    (hyps : hyps)
    (f : form) : form =
  let env = toenv hyps in

  let rec check (f : form) =
    match EcFol.sform_of_form f with
    | SFeq (f1, f2)
      when (Option.is_some @@ EcEnv.Circuit.lookup_bitstring env f1.f_ty)
           || (Option.is_some @@ EcEnv.Circuit.lookup_array env f1.f_ty) ->
      f_bool (circuit_simplify_equality ~st ~hyps ~pres f1 f2)
    | _ -> f_map (fun ty -> ty) check f
  in
  check f

let circ_valid (c : circuit) : bool = fst (circ_valid c)

let circuit_state_of_memenv
    ?(st : state = empty_state)
    (env : env)
    ((m, mt) as me : memenv) : state =
  match mt with
  | Lmt_concrete (Some {lmt_decl = decls}) ->
    let bnds =
      List.map
        (fun {ov_name; ov_type} ->
          match ov_name with
          | Some v -> begin
            try Some ((m, v), ctype_of_ty env ov_type)
            with CircError err -> propagate_circ_error (`Memenv me) err
          end
          | None -> None)
        decls
    in
    open_circ_lambda_pv st (List.filter_map identity bnds)
  | Lmt_concrete None -> st

let circuit_state_of_hyps
    ?(st : state = empty_state)
    ?(strict = false)
    (hyps : hyps) : state =
  let env = toenv hyps in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let st =
    List.fold_left
      (fun st (id, lk) ->
        EcEnv.notify env `Debug "Processing hyp: %s@." id.id_symb;
        match lk with
        (* If there is a memory, add all the variables from that memory into the translation state *)
        | EcBaseLogic.LD_mem mt -> circuit_state_of_memenv ~st env (id, mt)
        (* Initialized variable. 
           Check if body is convertible to circuit, if not just process it as uninitialized.
         *)
        | EcBaseLogic.LD_var (t, Some f) ->
          EcEnv.notify env `Debug "Assigning %a to %a@."
            EcPrinting.(pp_form ppe)
            f EcIdent.pp_ident id;
          begin
            try
              update_state st id (circuit_of_form st hyps f)
            with CircError e -> (
              EcEnv.notify env `Debug
                "Failed to translate hypothesis for var %s with error %a, \
                 skipping@."
                (tostring_internal id) (pp_circ_error ppe) e;
              try
                open_circ_lambda st [id, ctype_of_ty env t]
              with
              | ( CircError (AbstractTyBinding _)
                | CircError (MissingTyBinding _) ) as e
              ->
                if strict then raise e else st)
          end
          (* Uninitialized variable.
       Treat as input *)
        | EcBaseLogic.LD_var (t, None) -> begin
          try open_circ_lambda st [id, ctype_of_ty env t]
          with
          | (CircError (AbstractTyBinding _) | CircError (MissingTyBinding _))
            as e
          ->
            if strict then raise e else st
        end
        (* For things of the form a_ = a{&hr}, we assume the local variable takes precedence *)
        | EcBaseLogic.LD_hyp f -> begin
          match EcCallbyValue.norm_cbv (circ_red hyps) hyps f with
          | {
              f_node =
                Fapp
                  ( {f_node = Fop (p, _); _},
                    [{f_node = Fpvar (PVloc pv, m); _}; fv] );
            }
          | {
              f_node =
                Fapp
                  ( {f_node = Fop (p, _); _},
                    [fv; {f_node = Fpvar (PVloc pv, m); _}] );
            }
            when EcFol.op_kind p = Some `Eq -> begin
            try
              update_state_pv st m pv (circuit_of_form st hyps fv)
            with CircError e ->
              EcEnv.notify env `Debug
                "Failed to translate hypothesis %s => %a@\n\
                 With error: %a@\n\
                 Skipping...@\n"
                id.id_symb
                EcPrinting.(pp_form ppe)
                f (pp_circ_error ppe) e;
              st
          end
          | _ ->
            EcEnv.notify env `Debug
              "Hypothesis %s: %a does not match any circuit translation \
               patterns, skipping...@\n"
              id.id_symb
              EcPrinting.(pp_form ppe)
              f;
            st
        end
        | _ -> st)
      st
      (List.rev (tohyps hyps).h_local)
  in
  st

let clear_translation_caches () = EcLowCircuits.reset_backend_state ()
