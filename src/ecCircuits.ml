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
let debug : bool = EcLowCircuits.debug

(* -------------------------------------------------------------------- *)
let circ_red (hyps: hyps) = let base_red = EcReduction.full_red in
  {base_red with delta_p = (fun pth ->
  if (EcEnv.Circuit.reverse_operator (LDecl.toenv hyps) pth |> List.is_empty) then
    base_red.delta_p pth
  else
    `No)
} 

module AInvFHashtbl(Ctxt: sig val hyps: hyps end) = struct 
    type state = {
      level: int;
      subst: EcSubst.subst;
    } 

    let empty_state : state = {level = 0; subst = EcSubst.empty}

    let bruijn_idents : (int, ident) Map.t ref = ref Map.empty 

    let clean_bruijn_idents : unit -> unit =
      fun () -> bruijn_idents := Map.empty

    let ident_of_debruijn_level (i: int) : ident = 
      match Map.find_opt i !bruijn_idents with
      | Some id -> id
      | None -> let id = create (string_of_int i) in
        bruijn_idents := Map.add i id !bruijn_idents;
        id

    let add_to_state (id: ident) (ty: ty) (st: state) = 
      let new_id = ident_of_debruijn_level st.level in
      let level = st.level + 1 in
      let subst = EcSubst.add_flocal st.subst id (f_local new_id ty) in
      { level; subst }, new_id

    (* FIXME: maybe don't allow external calls with a state argument *)
    let rec hash (st:state) (f: form) : int =
      let hnode = match f.f_node with
      | Fquant (qnt, bnds, f)  ->
        let st, bnds = 
          List.fold_left_map (fun st (orig_id, gty) ->
            match gty with
            | GTty ty ->
              let st, new_id = add_to_state orig_id ty st in
              st, (new_id, gty)
            | _ -> 
              st, (orig_id, gty)
          ) st bnds 
        in Why3.Hashcons.combine2 (qt_hash qnt) (b_hash bnds) (hash st (EcSubst.subst_form st.subst f))
      | Fif (cond, tb, fb)  -> 
          let hash = hash st in
          Why3.Hashcons.combine2 (hash cond) (hash tb) (hash fb)
      | Fmatch (_, _, _)  -> assert false
      | Flet (lp, value, body)  -> 
          begin match lp with
          | LSymbol (orig_id, ty) -> 
            let hval = hash st value in
            let st, new_id = add_to_state orig_id ty st in
            let hbody = hash st (EcSubst.subst_form st.subst body) in
            let hlp = lp_hash (LSymbol (new_id, ty)) in
            Why3.Hashcons.combine2 hlp hval hbody
          | LTuple bnds -> 
            let hval = hash st value in
            let st, new_ids = List.fold_left_map (fun st (id, ty) -> add_to_state id ty st) st bnds in
            let hbody = hash st (EcSubst.subst_form st.subst body) in
            let hbinds = lp_hash @@ LTuple (List.combine new_ids (List.snd bnds)) in
            Why3.Hashcons.combine2 hbinds hval hbody
          | LRecord (_, _) -> assert false
          end
      | Fapp (op, args)  -> 
        let hop = hash st op in
        Why3.Hashcons.combine_list (hash st) hop args
      | Ftuple comps  -> 
        Why3.Hashcons.combine_list (hash st) 0 comps
      | Fproj (tp, i)  -> 
        Why3.Hashcons.combine (hash st tp) i 
      | FhoareF _hF -> 
          assert false
(*      FIXME: do we want this case and the one below?
        let hpre = doit st (hf_pr hF).inv in
        let hpo = doit st (hf_po hF).inv in
        let hf = x_hash hF.hf_f in
        let hm = id_hash hF.hf_m in
        Why3.Hashcons.combine3 hpre hpo hf hm
*)
      | FhoareS _hS -> 
          assert false
(*
        let hme = me_hash hS.hs_m in
        let hpre = doit st (hs_pr hS).inv in
        let hpo = doit st (hs_po hS).inv in
        let hs = s_hash
        f_hoareS me {inv=npre;m} hs.hs_s {inv=npo;m}
*)
      | FbdHoareF _  -> assert false
      | FbdHoareS _  -> assert false
      | FeHoareF _  -> assert false
      | FeHoareS _  -> assert false
      | FequivF _ef -> 
        assert false
(*      FIXME: do we want these cases? 
        let npre = doit st (ef_pr ef).inv in
        let npo = doit st (ef_po ef).inv in
        f_equivF {inv=npre;ml=ef.ef_ml;mr=ef.ef_mr} ef.ef_fl ef.ef_fr {inv=npo;ml=ef.ef_ml;mr=ef.ef_mr}
*)
      | FequivS _es  -> 
        assert false
(*
        let ml, mel = es.es_ml in
        let mr, mer = es.es_mr in
        let npre = doit st (es_pr es).inv in
        let npo = doit st (es_po es).inv in
        f_equivS mel mer {inv=npre;ml;mr} es.es_sl es.es_sr {inv=npo;ml;mr}
*)
      | FeagerF _  -> assert false
      | Fpr _ ->  assert false
      | Fint _ 
      | Flocal _ 
      | Fpvar (_, _) 
      | Fglob (_, _)
      | Fop (_, _) -> f_hash f (* FIXME: maybe do these cases as well? *)
      in Why3.Hashcons.combine hnode (ty_hash f.f_ty)

    module Htbl = Batteries.Hashtbl.Make(struct
    type t = form

    let equal f1 f2 = EcReduction.is_alpha_eq Ctxt.hyps f1 f2

    let hash f = hash empty_state f

    end)

  let clear htbl = 
    clean_bruijn_idents ();
    Htbl.clear htbl
end


(* -------------------------------------------------------------------- *)
type circuit_conversion_call = [
  | `Convert of form
  | `ToArg of form
  | `ExpandIter of form * form list
  | `Instr of instr
  | `Memenv of memenv
]

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
  | `OpK of EcFol.op_kind 
  | `Op of path 
  | `Quantif of quantif
  | `Match
  | `Glob
  | `ModGlob
  | `Record
  | `Hoare
  | `Instr
] 
| PropagateError of circuit_conversion_call * circuit_error 

exception CircError of circuit_error

let circ_error (err: circuit_error) =
  raise (CircError err)

let propagate_circ_error (call: circuit_conversion_call) (err: circuit_error) = 
  raise (CircError (PropagateError (call, err)))

(* FIXME: move this to EcPrinting maybe? *)
let pp_op_kind (fmt: Format.formatter) (opk: EcFol.op_kind) : unit =
  Format.fprintf fmt "%s"
  (match opk with
  | `Map_set -> "Map_set"
  | `Real_le -> "Real_le"
  | `Int_le -> "Int_le"
  | `Iff -> "Iff"
  | `Int_opp -> "Int_opp"
  | `Int_lt -> "Int_lt"
  | `Int_pow -> "Int_pow"
  | `And `Asym -> "And (&&)"
  | `And `Sym -> "And (/\\)"
  | `Map_cst -> "Map_cst"
  | `False -> "False"
  | `Eq -> "Eq"
  | `True -> "True"
  | `Int_mul -> "Int_mul"
  | `Real_inv -> "Real_inv"
  | `Real_add -> "Real_add"
  | `Int_edivz -> "Int_edivz"
  | `Or `Asym -> "Or (||)"
  | `Or `Sym -> "Or (\\/)"
  | `Not -> "Not"
  | `Int_add -> "Int_add"
  | `Map_get -> "Map_get"
  | `Real_lt -> "Real_lt"
  | `Real_opp -> "Real_opp"
  | `Real_mul -> "Real_mul"
  | `Imp -> "Imp")

let rec pp_circ_error ppe fmt (err: circuit_error) =
  let open EcPrinting in
  match err with
  | MissingTyBinding t ->
    Format.fprintf fmt "Missing type binding for ";
    begin match t with
    | `Path pth -> Format.fprintf fmt "type at path %a" pp_path pth
    | `Ty ty -> Format.fprintf fmt "type %a" (pp_type ppe) ty
    end
  | AbstractTyBinding t -> 
    Format.fprintf fmt "No concrete (only abstract) type binding for ";
    begin match t with
    | `Path pth -> Format.fprintf fmt "type at path %a" pp_path pth
    | `Ty ty -> Format.fprintf fmt "type %a" (pp_type ppe) ty
    end
  | MissingOpBinding pth ->
    Format.fprintf fmt "Missing op binding for operator at path %a" pp_path pth
  | MissingOpSpec pth -> 
    Format.fprintf fmt "Missing op spec binding for operator at path %a" pp_path pth
  | IntConversionFailure ->
    (* FIXME: check that this actually prints the form, otherwise add it *)
    Format.fprintf fmt "Failed to convert form to concrete integer"
  | MissingOpBody pth -> 
    Format.fprintf fmt "No body for operator at path %a" pp_path pth
  | CantConvertToConstant ->
    Format.fprintf fmt "Failed to reduce circuit to constant after composition (while attempting to compute)"
  | CantReadWriteGlobs ->
    Format.fprintf fmt "Cannot reason about programs which write to global variables using circuits"
  | BadFormForArg f ->
    Format.fprintf fmt "Form %a does not match any known conversion pattern from form to argument" (pp_form ppe) f
  | CantConvertToCirc reason -> 
    Format.fprintf fmt "Failed circuit conversion due to: ";
    begin match reason with
    | `Int -> Format.fprintf fmt "Encountered unexpected integer (maybe you are missing a binding?)"
    | `OpK opk -> Format.fprintf fmt "Don't know how to translate op kind: %a" pp_op_kind opk
    | `Op pth -> Format.fprintf fmt "Don't know how to convert operator at path %a to circuit (not concrete and does not match any known operator kind)" pp_path pth
    | `Quantif qnt -> Format.fprintf fmt "Encountered unexpected quantifier %s" (string_of_quant qnt)
    | `Match -> Format.fprintf fmt "Conversion of match statements not supported"
    | `Glob -> Format.fprintf fmt "Global variables not supported in conversion"
    | `ModGlob -> Format.fprintf fmt "Conversion of module globals not supported"
    | `Record -> Format.fprintf fmt "Conversion of records not supported"
    | `Hoare -> Format.fprintf fmt "Direct conversion of hoare statements not supported"
    | `Instr -> assert false
    end
  | PropagateError (call, e) -> 
    pp_circ_error ppe fmt e;
    Format.fprintf fmt "@\nWhile attemping ";
    begin match call with
    | `Convert f -> Format.fprintf fmt "conversion of form %a" (pp_form ppe) f
    | `ToArg f -> Format.fprintf fmt "conversion to arg of form %a" (pp_form ppe) f
    | `ExpandIter (f, args) -> Format.fprintf fmt "expansion of iter %a(%a)" (pp_form ppe) f (pp_list ", " (pp_form ppe)) args
    | `Instr inst -> Format.fprintf fmt "processing of instruction %a" (pp_instr ppe) inst
    | `Memenv (m, mt) -> Format.fprintf fmt "entering memory %a : %a" (pp_mem ppe) m (pp_memtype ppe) mt
    end
    

let ty_of_path (p: path) : ty =
  EcTypes.tconstr p []

let rec ctype_of_ty (env: env) (ty: ty) : ctype = 
  match ty.ty_node with
  | Ttuple tys -> CTuple (List.map (ctype_of_ty env) tys)
  | Tconstr (pth, []) when pth = EcCoreLib.CI_Bool.p_bool -> CBool
  | _ -> begin
    match EcEnv.Circuit.lookup_array_and_bitstring env ty with
    | Some ({size=(_, Some size_arr)}, {size=(_, Some size_bs)}) -> CArray {width=size_bs; count=size_arr}
    | None -> 
      begin match EcEnv.Circuit.lookup_bitstring_size env ty with
      | Some sz -> CBitstring sz
      | _ ->
          circ_error (MissingTyBinding (`Ty ty))
    end
    | Some ({size = (_, None)}, _) -> 
      circ_error (AbstractTyBinding (`Ty ty))
    | Some (_, {size = (_, None)}) -> 
      circ_error (AbstractTyBinding (`Ty ty))
  end

let width_of_type (env: env) (t: ty) : int =
  let cty = ctype_of_ty env t in
  EcLowCircuits.size_of_ctype cty
    
let input_of_type ~name (env: env) (t: ty) : circuit = 
  let ct = ctype_of_ty env t in
  input_of_ctype ~name ct 
    
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
      | None -> circ_error (MissingOpBinding p)
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
      | None -> circ_error (MissingOpBinding p)
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
      | None -> circ_error (MissingOpBinding p)
      end
    in
    (* assert false => should be guarded by a previous call to op_is_bsop *)
    match bnd with
    | _bs, `From -> assert false (* doesn't translate to circuit *)
    | {size = (_, Some size)}, `OfInt -> begin match args with
      | [ `Constant i ] ->
        circuit_of_zint ~size i
      | _args -> assert false (* Should be caught by EC typechecking + binding correctness *)
    end
    | {size = (_, None); type_=ty}, `OfInt -> 
      circ_error (AbstractTyBinding (`Path ty)) 
    | _bs, `To -> assert false (* doesn't translate to circuit *)
    | _bs, `ToSInt -> assert false (* doesn't translate to circuit *) 
    | _bs, `ToUInt -> assert false (* doesn't translate to circuit *)
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
      | None -> circ_error (MissingOpBinding p)
    end
    in
    (* assert false => should be guarded by a call to op_is_arrayop *)
    match op with
    | (_arr, `ToList) -> assert false (* We do not translate this to circuit *)
    | (_arr, `Get) -> begin match args with
      | [ `Circuit (({type_ = CArray _}, _inps) as arr); `Constant i] ->
        array_get arr (BI.to_int i)
      | _args -> assert false (* Should be caught by EC typechecking + binding correctness *)
    end
    | ({size = (_, Some size)}, `OfList) -> begin match args with 
      | [ `Circuit dfl; `List cs ] -> array_oflist cs dfl size
      | _args -> assert false (* Should be caught by EC typechecking + binding correctness *)
      end
    | ({size = (_, None); type_=ty}, `OfList) -> circ_error (AbstractTyBinding (`Path ty))
    | (_arr, `Set) -> begin match args with
      | [ `Circuit (({type_ = CArray _}, _) as arr); 
          `Constant i; 
          `Circuit (({type_ = CBitstring _}, _) as bs) ] ->
        array_set arr (BI.to_int i) bs
      | _args -> assert false (* Should be caught by EC typechecking + binding correctness *)
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
      | None -> circ_error (MissingOpSpec p) (* Will generally never happen *)
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
    circ_error (MissingOpBinding p) (* Will generally never happen *)
  in
  match op with
  | `Bitstring (_bs, _op) -> assert false (* Should be guarded by a call to op_is_base *)
  | `Array _ -> assert false  (* Should be guarded by a call to op_is_parametric_base *)
  | `BvOperator bvbnd -> circuit_of_bvop  env (`BvBind bvbnd)
  | `Circuit c -> circuit_from_spec env (`Bind c)
  
let circuit_of_op_with_args (env: env) (p: path) (args: arg list) : circuit  = 
  let op = try
    EcEnv.Circuit.reverse_operator env p |> List.hd
  with Failure _ -> 
    circ_error (MissingOpBinding p) (* Will generally never happen *)
  in
  match op with
  | `Bitstring bsbnd -> circuit_of_bsop env (`BSBinding bsbnd) args
  | `Array abnd -> circuit_of_arrayop env (`ABinding abnd) args 
  | `BvOperator bvbnd -> circuit_of_parametric_bvop env (`BvBind bvbnd) args 
  | `Circuit _c -> assert false (* FIXME PR: Do we want to have parametric operators coming from the spec?  *)


let type_has_bindings (env: env) (t: ty) : bool = 
  (Option.is_some (EcEnv.Circuit.lookup_array_and_bitstring env t)) ||
  (Option.is_some (EcEnv.Circuit.lookup_bitstring env t))

let int_of_form ?(redmode = EcReduction.full_red) (hyps: hyps) (f: form) : zint = 
  match f.f_node with 
  | Fint i -> i
  | _ -> 
    begin try 
      destr_int @@ EcCallbyValue.norm_cbv redmode hyps f
    with 
      DestrError "int" 
    | DestrError "destr_int" -> circ_error IntConversionFailure
    end

let rec form_list_of_form ?(env: env option) (f: form) : form list =
  match destr_op_app f with
  | (pc, _), [h; {f_node = Fop(p, _)}] when 
    pc = EcCoreLib.CI_List.p_cons && 
    p = EcCoreLib.CI_List.p_empty ->
    [h]
  | (pc, _), [h; t] when
    pc = EcCoreLib.CI_List.p_cons ->
    h::(form_list_of_form t)
  | _ -> 
    Option.may (fun env -> 
      EcEnv.notify env `Debug "Failed to destructure claimed list: %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f) env;
    raise (DestrError "list")

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
    EcEnv.notify env `Debug "Done generating functions!@.";
    let f = List.fold_left (fun f i -> 
      EcEnv.notify env `Debug "Expanding iter... Step #%d@.Form: %a@." (BI.to_int i)
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (toenv hyps))) f
      ;
      fn @!! [f_int i; f]
    ) base is in
    f
  | Fapp ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iter -> 
    let rep = int_of_form hyps rep in
    let is = List.init (BI.to_int rep) BI.of_int in
    let f = List.fold_left (fun f _i -> fn @!! [f]) base is in
    f
  | Fapp ({f_node = Fop (p, _)}, [fn; base; rep]) when p = EcCoreLib.CI_Int.p_fold -> 
    let rep = int_of_form hyps rep in
    let is = List.init (BI.to_int rep) BI.of_int in
    let f = List.fold_left (fun f _i -> fn @!! [f]) base is in
    f
  | _ -> raise (DestrError "iter")
  in
  EcEnv.notify env `Debug "Expanded iter form: @.%a@." EcPrinting.(pp_form ppenv) res;
  res

let circuit_of_form 
   (st      : state) (* Program variable values *)
   (hyps    : hyps) 
   (f_      : EcAst.form) 
  : circuit =

  let module AIFH = AInvFHashtbl(struct let hyps = hyps end) in

  (* Form level cache, local to each high-level call *)
  let cache : circuit AIFH.Htbl.t = AIFH.Htbl.create 700 in
  let op_cache : circuit Mp.t ref = ref Mp.empty in
  let redmode = circ_red hyps in
  let env = toenv hyps in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let fapply_safe f fs = 
    let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
    res
  in
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
        circ_error (MissingOpBody pth) 
    in
    let res = fapply_safe op args in 
    res
  in

  let rec arg_of_form (st: state) (f: form) : arg = 
    try
      match f.f_ty with
      | t when EcReduction.EqTest.is_int env t -> arg_of_zint (int_of_form f)
      | t when type_has_bindings env t -> 
          let f = doit st f in 
          arg_of_circuit f
      | {ty_node = Tfun(i_t, c_t)} when 
          i_t.ty_node = EcTypes.tint.ty_node &&
          type_has_bindings env c_t ->
          arg_of_init (fun i -> 
            let f = (fapply_safe f [f_int (BI.of_int i)]) in
            doit st f 
          )
      | {ty_node = Tconstr(p, [t])} when 
          p = EcCoreLib.CI_List.p_list &&
          type_has_bindings env t ->
          let cs = List.map (fun f -> doit st f) (form_list_of_form ~env f) in
          arg_of_circuits cs
      | _ -> EcLowCircuits.log st @@ Format.asprintf "Failed to convert form to arg: %a@." EcPrinting.(pp_form ppe) f; 
        circ_error (BadFormForArg f)
    with CircError e ->
      propagate_circ_error (`ToArg f) e

  (* State does not get backward propagated so it is not returned *)
  and doit (st: state) (f_: form) : circuit =  
    try begin
    match f_.f_node with
    | Fint _z -> circ_error (CantConvertToCirc `Int)

    | Fif (c_f, t_f, f_f) -> 
        let t = doit st t_f in
        let f = doit st f_f in
        let c = doit st c_f in
        circuit_ite ~c ~t ~f

    | Flocal idn -> 
        state_get st idn

    | Fop (pth, _) -> 
      begin
      if pth = EcCoreLib.CI_Witness.p_witness then 
          (EcEnv.notify env `Debug "Assigning witness to var of type %a@." 
          EcPrinting.(pp_type ppe) f_.f_ty;
          circuit_uninit env (f_.f_ty))
      else
      match Mp.find_opt pth !op_cache with
      | Some op -> 
        op
      | None -> 
      if op_is_base env pth then
        let circ = circuit_of_op env pth in
        op_cache := Mp.add pth circ !op_cache;
        circ 
      else
        let circ = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
          doit st f
        | _ -> 
        begin match EcFol.op_kind (destr_op f_ |> fst) with
          | Some `True -> 
            (circuit_true :> circuit)
          | Some `False ->
            (circuit_false :> circuit)
          | Some opk -> circ_error (CantConvertToCirc (`OpK opk))
          | None -> circ_error (CantConvertToCirc (`Op (destr_op f_ |> fst))) 
        end
        in 
        op_cache := Mp.add pth circ !op_cache;
        circ
    end
    | Fapp (f, fs) -> 
    (* TODO: Maybe add cache statistics? *)
    (* TODO: Maybe cache all forms       *)
    begin match AIFH.Htbl.find_opt cache f_ with 
    | Some circ -> circ
    | None -> 
      let circ = begin match f with
        | {f_node = Fop (pth, _)} when op_is_parametric_base env pth -> 
          let args = List.map (arg_of_form st) fs in 
          circuit_of_op_with_args env pth args

        (* For dealing with iter cases: *)
        | {f_node = Fop _} when form_is_iter f_ -> 
          trans_iter st hyps f fs

        | {f_node = Fop (_p, _)} when not (List.for_all (fun f -> f.f_ty.ty_node <> EcTypes.tint.ty_node) fs) ->
            doit st (propagate_integer_arguments f fs)

        | {f_node = Fop _} -> 
        (* Assuming correct types coming from EC *)
        begin match EcFol.op_kind (destr_op f |> fst), fs with
          | Some `Eq, [f1; f2] -> 
            let c1 = doit st f1 in
            let c2 = doit st f2 in
            (circuit_eq c1 c2 :> circuit)
          | Some `Not, [f] -> 
            let c = doit st f in
            circuit_not c 
          | Some `True, [] ->
            (circuit_true :> circuit)
          | Some `False, [] ->
            (circuit_false :> circuit)
          | Some `Imp, [f1; f2] -> 
            let c1 = doit st f1 in
            let c2 = doit st f2 in
            (circuit_or (circuit_not c1) c2 :> circuit)
          | Some (`And _), [f1; f2] -> 
            let c1 = doit st f1 in
            let c2 = doit st f2 in
            (circuit_and c1 c2 :> circuit)
          | Some (`Or _), [f1; f2] -> 
            let c1 = doit st f1 in
            let c2 = doit st f2 in
            (circuit_or c1 c2 :> circuit)
          | Some `Iff, [f1; f2] -> 
            let c1 = doit st f1 in
            let c2 = doit st f2 in
            (circuit_or (circuit_and c1 c2) (circuit_and (circuit_not c1) (circuit_not c2)) :> circuit)
          (* Recurse down into definition *)
          | _ -> 
            let f_c = doit st f in
            let fcs = List.map (doit st) fs in
            circuit_compose f_c fcs
        end
        (* Recurse down into definition *)
        | _ -> 
          let f_c = doit st f in
          let fcs = List.map (doit st) fs in
          circuit_compose f_c fcs
      end in
        AIFH.Htbl.add cache f_ circ;
        circ
      end
      
    | Fquant (qnt, binds, f) -> 
      (* FIXME Does this type conversion make sense? *)
      let binds = List.map (fun (idn, t) -> (idn, gty_as_ty t |> ctype_of_ty env)) binds in 
      begin match qnt with
      | Lforall 
      | Llambda -> circ_lambda_oneshot st binds (fun st -> doit st f) (* FIXME: look at this interaction *)
      | Lexists -> circ_error (CantConvertToCirc (`Quantif qnt))
      (* FIXME: Do we want to handle existentials? *)
      end

    | Fproj (f, i) ->
        let ftp = doit st f in
        (circuit_tuple_proj ftp i :> circuit)

    | Fmatch  (_f, _fs, _ty) -> circ_error (CantConvertToCirc `Match)

    | Flet    (LSymbol (id, _t), v, f) -> 
      let vc = doit st v in
      let st = update_state st id vc in
      doit st f

    | Flet    (LTuple vs, v, f) -> 
      let vc = doit st v in
      let comps = circuits_of_circuit_tuple vc in
      let st = List.fold_left2 (fun st (id, _t) vc ->
        update_state st id vc)
        st
        vs
        comps
      in doit st f

    | Flet (LRecord _, _, _) -> circ_error (CantConvertToCirc `Record)

    | Fpvar   (pv, mem) -> 
      let v = match pv with
      | PVloc v -> v
      (* FIXME: Should globals be supported? *)
      | _ -> circ_error (CantConvertToCirc `Glob)
      in 
      let v = match state_get_pv_opt st mem v with
      | Some v -> v
      | None -> 
          EcEnv.notify env `Debug "Assigning unassigned program variable %a of type %a@." EcPrinting.(pp_pv ppe) pv EcPrinting.(pp_type ppe) f_.f_ty; 
          circuit_uninit env f_.f_ty (* Allow uninitialized program variables *)
      in
      v

    | Fglob (_id, _mem) -> circ_error (CantConvertToCirc `ModGlob)

    | Ftuple comps -> 
      let comps = 
        List.map (fun comp -> doit st comp) comps 
      in
      (circuit_tuple_of_circuits comps :> circuit)

    | FhoareF  _
    | FhoareS  _
    | FbdHoareF  _
    | FbdHoareS  _
    | FeHoareF  _
    | FeHoareS  _
    | FequivF  _
    | FequivS  _
    | FeagerF  _
    | Fpr _ -> circ_error (CantConvertToCirc `Hoare) 
    (* FIXME: do we want to allow conversion of hoare statements? 
        Probably not at this point
     *)
    end
    with
    | CircError e ->
      propagate_circ_error (`Convert f_) e

  and trans_iter (st: state) (hyps: hyps) (f: form) (fs: form list) : circuit =
    try
      (* FIXME: move auxiliary function out of the definitions *)
      let redmode = circ_red hyps in
      let fapply_safe f fs = 
        let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
        res
      in
      match f, fs with
      | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iteri -> 
        let rep = int_of_form rep in
        let fs = List.init (BI.to_int rep) (fun i ->
          fapply_safe fn [f_int (BI.of_int i)]
        ) in
        List.fold_lefti (fun f i fn -> 
          EcEnv.notify env `Debug "Translating iteri... Step #%d@." i;
          let fn = doit st fn in
          circuit_compose fn [f]
        ) (doit st base) fs
      (* This is defined in terms of iteri, so it should get expanded and use the case above *)
      (* | ({f_node = Fop (p, _)}, [rep; fn; base]) when p = EcCoreLib.CI_Int.p_iter -> assert false  *)
      | ({f_node = Fop (p, _)}, [fn; start_val; reps]) when p = EcCoreLib.CI_Int.p_fold -> 
        let reps = int_of_form reps |> BI.to_int in
        let fn = doit st fn in
        let start_val = doit st start_val in
        List.fold_left (fun acc f ->
          circuit_compose f [acc]
        ) start_val (List.make reps fn)
      | _ -> raise (DestrError "iter")
    with CircError e ->
      propagate_circ_error (`ExpandIter (f, fs)) e
  in 
  let res = doit st f_  in
  (* State cleanup *)
  begin
    op_cache := Mp.empty;
    AIFH.clear cache
  end;
  res
  

let circuit_simplify_equality ?(do_time = true) ~(st: state) ~(hyps: hyps) ~(pres: circuit list) (f1: form) (f2: form) : bool =
  let tm = ref (Unix.gettimeofday ()) in
  let env = toenv hyps in
  let time (env: env) (t: float ref) (msg: string) : unit =
    let new_t = Unix.gettimeofday () in
    EcEnv.notify ~immediate:true env `Info "[W] %s, took %f s@." msg (new_t -. !t); 
    t := new_t
  in

  EcEnv.notify env `Debug "Filletting circuit...@.";
  let c1 = circuit_of_form st hyps f1 |> state_close_circuit st in
  if do_time then time env tm "Left side circuit generation done";
  let c2 = circuit_of_form st hyps f2 |> state_close_circuit st in
  if do_time then time env tm "Right side circuit generation done";

  let pres = List.map (state_close_circuit st) pres in (* Assumes pres come open *)
  assert (Option.is_none @@ circuit_has_uninitialized c1);
  assert (Option.is_none @@ circuit_has_uninitialized c2);
  let posts = circuit_eqs c1 c2 in
  if do_time then time env tm "Done with postcondition circuit generation";

  EcEnv.notify env `Debug "Number of checks before batching: %d@." (List.length posts);
  let posts = batch_checks ~mode:`BySub posts in
  EcEnv.notify env `Debug "Number of checks after batching: %d@." (List.length posts);
  if do_time then time env tm "Done with lane compression";
  if fillet_tauts pres posts then 
    begin
      if do_time then time env tm "Done with equivalence checking (structural equality + SMT)";
      true
    end
  else 
    begin
      if do_time then time env tm "Failed equivalence check";
      false
    end

(* FIXME: add support for spec bindings for abstract/opaque operators 
    = convert from Fop rather than from op body *)
let circuit_of_path (st: state) (hyps: hyps) (p: path) : circuit =
  let f = EcEnv.Op.by_path p (toenv hyps) in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> circ_error (MissingOpBody p)
  in
  circuit_of_form st hyps f

let vars_of_memtype (mt : memtype) =
  let Lmt_concrete lmt = mt in
  List.filter_map (function 
    | { ov_name = Some name; ov_type = ty } ->
      Some { v_name = name; v_type = ty; }
    | _ -> None
  ) (Option.get lmt).lmt_decl 
  

let process_instr (hyps: hyps) (mem: memory) ~(st: state) (inst: instr) : state =
  EcEnv.notify (toenv hyps) `Debug "[W] Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv (toenv hyps))) inst;
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) -> 
      let c = ((ss_inv_of_expr mem e).inv |> circuit_of_form st hyps) in
      let st = update_state_pv st mem v c in
      st
      (* EcEnv.notify env `Debug "[W] Took %f seconds@." (Unix.gettimeofday() -. start); *)
    | Sasgn (LvTuple (vs), {e_node = Etuple es; _}) when List.compare_lengths vs es = 0 ->
      let st = List.fold_left (fun st (v, e) ->
        let c = ((ss_inv_of_expr mem e).inv |> circuit_of_form st hyps) in
        let st = update_state_pv st mem v c in
        st
      ) st
        (List.combine 
          (List.map (function 
          | (PVloc v, _ty) -> v
          | _ -> circ_error (CantConvertToCirc `Glob)) vs) 
        es) in
      st
    | Sasgn (LvTuple (vs), e) ->
      let tp = ((ss_inv_of_expr mem e).inv |> circuit_of_form st hyps) in
      let comps = circuits_of_circuit_tuple tp in
      let st = List.fold_left2 (fun st (pv, _ty) c -> 
        let v = match pv with
        | PVloc v -> v
        | _ -> circ_error (CantConvertToCirc `Glob)
        in
        update_state_pv st mem v c 
        ) st vs (comps :> circuit list)
      in 
      st
    | _ -> 
      circ_error (CantConvertToCirc `Instr)
  with 
  | CircError e ->
    propagate_circ_error (`Instr inst) e

(* FIXME: check if memory is the right one in calls to state *)
let instrs_equiv
   (hyps       : hyps                )
   ((mem, _mt) : memenv              )
  ?(keep       : EcPV.PV.t option    )
   (st         : state               )
   (s1         : instr list          )
   (s2         : instr list          ) : bool
=
  let env = LDecl.toenv hyps in

  let rd, rglobs = EcPV.PV.elements (EcPV.is_read  env (s1 @ s2)) in
  let wr, wglobs = EcPV.PV.elements (EcPV.is_write env (s1 @ s2)) in

  if not (List.is_empty rglobs && List.is_empty wglobs) then
    circ_error CantReadWriteGlobs;

  if not (List.for_all (EcTypes.is_loc -| fst) (rd @ wr)) then
    circ_error CantReadWriteGlobs;

  let inputs = List.map (fun (pv, ty) -> { v_name = EcTypes.get_loc pv; v_type = ty; }) (rd @ wr) in
  let inputs = List.map (fun {v_name; v_type} -> (create v_name, ctype_of_ty env v_type)) inputs in
  let st = open_circ_lambda st inputs in

  let st1 = List.fold_left (fun st -> process_instr hyps mem ~st) st s1 in
  let st2 = List.fold_left (fun st -> process_instr hyps mem ~st) st s2 in

  let st1 = close_circ_lambda st1 in 
  let st2 = close_circ_lambda st2 in
  (* FIXME: what was the intended behaviour for keep? *)
  match keep with
  | Some pv -> 
    let vs = EcPV.PV.elements pv |> fst in
    let vs = List.map (function 
      | (PVloc v, ty) -> (v, ty)
      | _ -> circ_error (CantConvertToCirc `Glob)
      ) vs 
    in List.for_all (fun (var, _ty) -> 
      let circ1 = state_get_pv_opt st1 mem var in
      let circ2 = state_get_pv_opt st2 mem var in
      match circ1, circ2 with
      | None, None -> true
      | None, Some _
      | Some _, None -> false (* Variable only defined on one of the blocks (and not in the prelude) *)
      | Some circ1, Some circ2 -> circ_equiv circ1 circ2 
    ) vs
  | None -> state_get_all_memory st mem |> List.for_all (fun (var, _) -> 
    let circ1 = state_get_pv st1 mem var in
    let circ2 = state_get_pv st2 mem var in
    circ_equiv circ1 circ2 
  )

(* FIXME: change memory -> memenv Why?            *)
let state_of_prog ?(close = false) (hyps: hyps) (mem: memory) ~(st: state) (proc: instr list)  : state =
  let st = 
    List.fold_left (fun st -> process_instr hyps mem ~st) st proc
  in
  if close then 
  close_circ_lambda st 
  else st

let circ_simplify_form_bitstring_equality
  ?(st: state = empty_state) 
  ?(pres: circuit list = [])
  (hyps: hyps) 
  (f: form)
  : form =
  let env = toenv hyps in

  let rec check (f : form) =
    match EcFol.sform_of_form f with
    | SFeq (f1, f2)
         when (Option.is_some @@ EcEnv.Circuit.lookup_bitstring env f1.f_ty)
           || (Option.is_some @@ EcEnv.Circuit.lookup_array env f1.f_ty)
      ->
      f_bool (circuit_simplify_equality ~st ~hyps ~pres f1 f2)
    | _ -> f_map (fun ty -> ty) check f 
  in check f


(* Mli stuff needed: *)
let compute ~(sign: bool) (c: circuit) (args: zint list) : zint = 
  match compute ~sign c (List.map (fun z -> arg_of_zint z) args) with
  | Some z -> z
  | None -> circ_error CantConvertToConstant

let circ_equiv ?(pcond: circuit option) c1 c2 = 
  circ_equiv ?pcond c1 c2

let circ_sat = circ_sat
let circ_taut = circ_taut

let circuit_to_string ((circ, inps): circuit) : string = Format.asprintf "(%a => %a)" EcPrinting.(pp_list ", " pp_cinp) inps pp_circ circ
let circuit_ueq = (fun c1 c2 -> (circuit_eq c1 c2 :> circuit))
let circuit_has_uninitialized = circuit_has_uninitialized

let circuit_to_file = circuit_to_file

let circuit_slice (c: circuit) (size: int) (offset: int) = 
  circuit_slice ~size c offset

let circuit_flatten (({type_; _}, _) as c: circuit) = 
  convert_type (CBitstring (size_of_ctype type_)) c

let state_get = state_get_pv
let state_get_opt = state_get_pv_opt
let state_get_all = fun st -> state_get_all_pv st |> List.snd

let circuit_state_of_memenv ?(st: state = empty_state) (env:env) ((m, mt) as me: memenv) : state =
  match mt with
  | (Lmt_concrete Some {lmt_decl=decls}) ->
      let bnds = List.map (fun {ov_name; ov_type} ->
        match ov_name with
        | Some v -> 
          begin try
            Some ((m, v), ctype_of_ty env ov_type)
          with CircError err -> propagate_circ_error (`Memenv me) err
          end
        | None -> None
      ) decls in
      open_circ_lambda_pv st (List.filter_map identity bnds)
  | Lmt_concrete None -> st

let circuit_state_of_hyps ?(st: state = empty_state) ?(strict = false) (hyps: hyps) : state = 
  let env = toenv hyps in
  let ppe = EcPrinting.PPEnv.ofenv env in
  let st = List.fold_left (fun st (id, lk) ->
    EcEnv.notify env `Debug "Processing hyp: %s@." (id.id_symb);
    match lk with
    (* If there is a memory, add all the variables from that memory into the translation state *)
    | EcBaseLogic.LD_mem mt -> circuit_state_of_memenv ~st env (id, mt)

    (* Initialized variable. 
       Check if body is convertible to circuit, if not just process it as uninitialized.
       TODO: Maybe do a first pass on this, check convertibility and remove duplicates? *)
    | EcBaseLogic.LD_var (t, Some f) -> 
      EcEnv.notify env `Debug "Assigning %a to %a@." EcPrinting.(pp_form ppe) f EcIdent.pp_ident id;
      begin try
        update_state st id (circuit_of_form st hyps f)
      (* FIXME PR: Should only catch circuit translation errors, hack *)
      with CircError e ->
        EcEnv.notify env `Debug "Failed to translate hypothesis for var %s with error %a, skipping@." (tostring_internal id) (pp_circ_error ppe) e;
        try 
          open_circ_lambda st [(id, ctype_of_ty env t)]
        (* FIXME PR: Should only catch circuit translation errors, hack *)
        with 
          | CircError (AbstractTyBinding _) 
          | CircError (MissingTyBinding _) as e ->
          if strict then raise e else st
      end

      (* Uninitialized variable.
       Treat as input *)
    | EcBaseLogic.LD_var (t, None) -> 
      begin try
        open_circ_lambda st [(id, ctype_of_ty env t)]
      with 
        | CircError (AbstractTyBinding _) 
        | CircError (MissingTyBinding _) as e ->
        if strict then raise e else st
      end

    (* For things of the form a_ = a{&hr}, we assume the local variable takes precedence *)
    | EcBaseLogic.LD_hyp f -> 
      begin match (EcCallbyValue.norm_cbv (circ_red hyps) hyps f) with
      | {f_node=Fapp ({f_node = Fop (p, _); _}, [{f_node = Fpvar (PVloc pv, m); _}; fv])} 
      | {f_node=Fapp ({f_node = Fop (p, _); _}, [fv; {f_node = Fpvar (PVloc pv, m); _}])} when EcFol.op_kind p = Some `Eq ->
        begin try
          update_state_pv st m pv (circuit_of_form st hyps fv)
        (* FIXME PR: Should only catch circuit translation errors, hack *)
        with CircError e ->
          EcEnv.notify env `Debug "Failed to translate hypothesis %s => %a@\nWith error: %a@\nSkipping...@\n" 
            id.id_symb EcPrinting.(pp_form ppe) f (pp_circ_error ppe) e;
          st
        end
      | _ -> 
        EcEnv.notify env `Debug "Hypothesis %s: %a does not match any circuit translation patterns, skipping...@\n"
          id.id_symb EcPrinting.(pp_form ppe) f;
        st
      end
        
      | _ -> st 
  ) st (List.rev (tohyps hyps).h_local)
  in 
  st

let clear_translation_caches () =
  EcLowCircuits.reset_backend_state ();
