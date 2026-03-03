(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcPath
open EcEnv
open EcAst
open EcCoreFol
open EcCoreGoal
open EcIdent
open LDecl
open EcLowCircuits

type ident = EcIdent.t

type bvtype = 
  [ `W of int
  | `Int ]

type op = 
  [ `Add
  | `Mul 
  | `Ite
  | `Extend of (int * bool)
  | `Rem of bool
  | `Div of bool
  | `Le of bool
  | `Lt of bool
  | `Shls      
  | `Shl
  | `ASliceSet 
  | `And
  | `Extract   
  | `Map
  | `AInit     
  | `Sub
  | `Get       
  | `Ror
  | `Concat
  | `Truncate of int
  | `Opp
  | `Shrs of int * bool (* Size of first operand + signed? *)
  | `Not
  | `Or        
  | `Init
  | `Insert    
  | `Xor
  | `Shr of bool
  | `Mul
  | `Rol       
  | `A2B
  | `ASliceGet 
  | `B2A    
  | `Eq ]


let op_to_string (op: op) = 
  match op with 
  | `Extend (sz, true )    -> Format.sprintf "SExtend<%d>" sz
  | `Extend (sz, false)    -> Format.sprintf "UExtend<%d>" sz
  | `Rem true       -> "SRem"
  | `Rem false      -> "URem"
  | `Div true       -> "SDiv"
  | `Div false      -> "UDiv"
  | `Add       -> "Add"
  | `Lt true         -> "SLt"
  | `Lt false        -> "ULt"
  | `Shls      -> "Shls"
  | `Shl       -> "Shl"
  | `ASliceSet -> "ASliceSet"
  | `And       -> "And"
  | `Extract   -> "Extract"
  | `Map       -> "Map"
  | `AInit     -> "AInit"
  | `Sub       -> "Sub"
  | `Get       -> "Get"
  | `Ror       -> "Ror"
  | `Le true        -> "SLe"
  | `Le false       -> "ULe"
  | `Concat    -> "Concat"
  | `Truncate sz -> Format.sprintf "Truncate<%d>" sz
  | `Opp       -> "Opp"
  | `Shrs (_, true)  -> "Shras"
  | `Shrs (_, false) -> "Shras"
  | `Not       -> "Not"
  | `Or        -> "Or"
  | `Init      -> "Init"
  | `Insert    -> "Insert"
  | `Xor       -> "Xor"
  | `Shr true       -> "Shra"
  | `Shr false      -> "Shrl"
  | `Mul       -> "Mul"
  | `Rol       -> "Rol"
  | `A2B       -> "A2B"
  | `ASliceGet -> "ASliceGet"
  | `B2A       -> "B2A"
  | `Ite       -> "if"
  | `Eq        -> "eq"

type formula = 
  | Base of ident * bvtype
  | Const of int * bvtype
  | Op of op * (formula list)

let op_of_path (env: env) (p: path) : op =
  match EcEnv.Circuit.lookup_bvoperator_path env p with
  | Some { kind = `Extend ((_, Some bsz), (_, Some sz), sign); _} -> `Extend (sz - bsz, sign)
  | Some { kind = `Rem ((_, Some _), sign); _}        -> `Rem sign
  | Some { kind = `Div ((_, Some _), sign); _}        -> `Div sign
  | Some { kind = `Add ((_, Some _)); _}        -> `Add
  | Some { kind = `Lt ((_, Some _), sign); _}      -> `Lt sign
  | Some { kind = `Shls _; _}       -> `Shls
  | Some { kind = `Shl _; _}        -> `Shl
  | Some { kind = `ASliceSet _; _}  -> `ASliceSet
  | Some { kind = `And _; _}        -> `And
  | Some { kind = `Extract _; _}    -> `Extract
  | Some { kind = `Map _; _}        -> `Map
  | Some { kind = `AInit _; _}      -> `AInit
  | Some { kind = `Sub _; _}        -> `Sub
  | Some { kind = `Get _; _}        -> `Get
  | Some { kind = `Ror _; _}        -> `Ror
  | Some { kind = `Le ((_, Some _), sign); _}     -> `Le sign
  | Some { kind = `Concat _; _}     -> `Concat
  | Some { kind = `Truncate ((_, Some _), (_, Some sz)); _} -> `Truncate sz
  | Some { kind = `Opp _; _}        -> `Opp
  | Some { kind = `Shrs ((_, Some sz), _, sign); _}       -> `Shrs (sz, sign)
  | Some { kind = `Not _; _}        -> `Not
  | Some { kind = `Or _; _}         -> `Or
  | Some { kind = `Init _; _}       -> `Init
  | Some { kind = `Insert _; _}     -> `Insert
  | Some { kind = `Xor _; _}        -> `Xor
  | Some { kind = `Shr ((_, Some _), sign); _}  -> `Shr sign
  | Some { kind = `Mul _; _}        -> `Mul
  | Some { kind = `Rol _; _}        -> `Rol
  | Some { kind = `A2B _; _}        -> `A2B
  | Some { kind = `ASliceGet _; _}  -> `ASliceGet
  | Some { kind = `B2A _; _}        -> `B2A
  | _ -> Format.eprintf "Failed for path %s@." (EcPath.tostring p);
    assert false

let bvtype_of_ty env ty : bvtype = 
  if ty = EcTypes.tint then
    `Int
  else `W (size_of_ctype @@ EcCircuits.ctype_of_ty env ty)

let pp_bvtype fmt t : unit =
  match t with
  | `W i -> Format.fprintf fmt "@%d" i
  | `Int -> Format.fprintf fmt "Z"

let rec pp_formula fmt f : unit =
  match f with
  | Base (id, t) -> Format.fprintf fmt "%s[%a]" id.id_symb pp_bvtype t
  | Op (op, args) -> Format.fprintf fmt "%s(@[<hov 2>%a@])" (op_to_string op) 
    EcPrinting.(pp_list "," pp_formula) args
  | Const (i, t) -> Format.fprintf fmt "%d[%a]" i pp_bvtype t

let bvformula_of_form (hyps: hyps) (f: form) : formula = 
  let env = toenv hyps in

  let pv_cache : (prog_var * ident, ident) Map.t ref = ref Map.empty in
  let let_binds : (ident, formula) Map.t = Map.empty in

  let rec doit lbinds (f_: form) =
    match f_.f_node with
    | Fquant (_, _, _) -> assert false
    | Fif (c, t, f) -> 
      let c = doit lbinds c in
      let t = doit lbinds t in
      let f = doit lbinds f in
      Op (`Ite, [c; t; f])
    | Fmatch (_, _, _) -> assert false
    | Flet (lp, v, e) -> begin 
      match lp with
      | LSymbol (id, _t) -> 
        let v_bv = doit lbinds v in
        let lbinds = Map.add id v_bv lbinds in
        doit lbinds e
      | _ -> assert false
      end
    | Fint z -> Const (BI.to_int z, `Int)
    | Flocal lv -> begin match Map.find_opt lv lbinds with
      | Some f -> f
      | None -> Base (lv, bvtype_of_ty env f_.f_ty)
      end
    | Fpvar (pv, m) -> 
      let id = match Map.find_opt (pv, m) !pv_cache with
      | Some id -> id
      | None -> let name = match pv with
        | PVglob _ -> assert false
        | PVloc s -> s
        in let id = EcIdent.create name in
        pv_cache := Map.add (pv, m) id !pv_cache;
        id
      in
      Base (id, bvtype_of_ty env f_.f_ty)
    | Fglob (_, _) -> assert false
    | Fop (_, _) -> assert false
    | Fapp ({f_node = Fop(p, _);}, [arg]) when (EcPath.toqsymbol p |> snd) = "of_int" ->
      Const (EcCircuits.int_of_form hyps arg |> BI.to_int, 
             `W (EcEnv.Circuit.lookup_bitstring_size env f_.f_ty |> Option.get))
    | Fapp (_, _) -> 
        let (fp, _), fs = destr_op_app f_ in
        let args = List.map (doit lbinds) fs in
        begin match EcFol.op_kind fp with
        | Some `Eq ->
          Op (`Eq, args)
        | _ -> 
          let op = op_of_path env fp in
          Op (op, args)
        end
    | Ftuple _ -> assert false

    | Fproj (_, _) -> assert false

    | FhoareF _ -> assert false
    | FhoareS _ -> assert false
    | FbdHoareF _ -> assert false
    | FbdHoareS _ -> assert false
    | FeHoareF _ -> assert false
    | FeHoareS _ -> assert false
    | FequivF _ -> assert false
    | FequivS _ -> assert false
    | FeagerF _ -> assert false
    | Fpr _ -> assert false
  in 
  doit let_binds f


let check_formula_BWZ (f: formula) : bool = 
  let open Bitwuzla_cxx in
  let options = Options.default () in
  Options.set options Produce_models true;
  let bitwuzla = Solver.create options in


  let bvterm_of_int (size: int) (v: int) : Term.t =
    mk_bv_value_int (mk_bv_sort size) v
  in

  let bvterm_of_ident (size: int) (id: ident) : Term.t = 
    mk_const (mk_bv_sort size) ~symbol:(id.id_symb ^ "#" ^ (string_of_int id.id_tag))
  in

  let size_of_bvtype ty = 
    match ty with 
    | `W s -> s
    | _ -> assert false
  in

  let base_terms : (ident, Term.t) Map.t ref = ref Map.empty in

  let rec doit (f: formula) : Term.t = 
    match f with
    | Base (id, t) -> 
      begin match Map.find_opt id !base_terms with
      | Some t -> t
      | None -> let t = bvterm_of_ident (size_of_bvtype t) id in
        base_terms := Map.add id t !base_terms;
        t
      end
    | Const (v, t) -> bvterm_of_int (size_of_bvtype t) v
    | Op (op, args) ->
      let args = List.map doit args in
      begin try begin match op, args with
      | `Extend (sz, true),  [bv] -> mk_term1_indexed1 Kind.Bv_sign_extend bv sz
      | `Extend (sz, false), [bv] -> mk_term1_indexed1 Kind.Bv_zero_extend bv sz
      | `Rem true,  [bv1; bv2] -> mk_term2 Kind.Bv_srem bv1 bv2
      | `Rem false, [bv1; bv2] -> mk_term2 Kind.Bv_urem bv1 bv2
      | `Div true , [bv1; bv2] -> mk_term2 Kind.Bv_sdiv bv1 bv2
      | `Div false, [bv1; bv2] -> mk_term2 Kind.Bv_udiv bv1 bv2 
      | `Add, [bv1; bv2] -> mk_term2 Kind.Bv_add bv1 bv2
      | `Shl, [bv1; bv2] -> mk_term2 Kind.Bv_shl bv1 bv2
      | `Shls, args -> assert false
      | `Lt true,  [bv1; bv2] -> mk_term2 Kind.Bv_slt bv1 bv2
      | `Lt false, [bv1; bv2] -> mk_term2 Kind.Bv_ult bv1 bv2
      | `ASliceSet, args -> assert false
      | `And, [bv1; bv2] -> mk_term2 Kind.Bv_and bv1 bv2
      | `Extract, args -> assert false
      | `Map, args -> assert false
      | `Ite, [c; t; f] -> assert false
      | `AInit, args -> assert false
      | `Sub, [bv1; bv2] -> mk_term2 Kind.Bv_sub bv1 bv2
      | `Ror, [bv1; bv2] -> mk_term2 Kind.Bv_ror bv1 bv2
      | `Get, args -> assert false
      | `Le true , [bv1; bv2] -> mk_term2 Kind.Bv_sle bv1 bv2
      | `Le false, [bv1; bv2] -> mk_term2 Kind.Bv_ule bv1 bv2
      | `Opp, [bv] -> mk_term1 Kind.Bv_neg bv
      | `Truncate sz, [bv] -> mk_term1_indexed2 Kind.Bv_extract bv (sz-1) 0
      | `Concat, [bv1; bv2] -> mk_term2 Kind.Bv_concat bv1 bv2
      | `Shrs (sz, true ), [bv1; bv2] -> 
        mk_term2 Kind.Bv_ashr bv1 (mk_term1_indexed1 Kind.Bv_zero_extend bv2 (sz - 8))
      | `Shrs (sz, false), [bv1; bv2] -> 
        mk_term2 Kind.Bv_shr bv1 (mk_term1_indexed1 Kind.Bv_zero_extend bv2 (sz - 8))
      | `Or, [bv1; bv2] -> mk_term2 Kind.Bv_or bv1 bv2
      | `Not, [bv] -> mk_term1 Kind.Bv_not bv
      | `Shr true , [bv1; bv2] -> mk_term2 Kind.Bv_ashr bv1 bv2
      | `Shr false, [bv1; bv2] -> mk_term2 Kind.Bv_shr bv1 bv2
      | `Xor, [bv1; bv2] -> mk_term2 Kind.Bv_xor bv1 bv2
      | `Insert, args -> assert false
      | `Init, args -> assert false
      | `Mul, [bv1; bv2] -> mk_term2 Kind.Bv_mul bv1 bv2
      | `Rol, [bv1; bv2] -> mk_term2 Kind.Bv_rol bv1 bv2
      | `A2B, args -> assert false
      | `ASliceGet, args -> assert false
      | `B2A, args -> assert false
      | `Eq, [bv1; bv2] -> mk_term2 Kind.Equal bv1 bv2
      | _ -> assert false
      end
    with e ->
      Format.eprintf "Failed on formula %a@." pp_formula f;
      raise e
    end
  in 
  Solver.assert_formula bitwuzla (mk_term1 Kind.Not @@ doit f);

  let get_val (bv: Term.t) : Term.t =
    Solver.get_value bitwuzla bv 
  in
  match Solver.check_sat bitwuzla with
  | Sat -> 
    Map.iter (fun _ t ->
      Format.eprintf "%a: %a@." Term.pp t Term.pp (get_val t)) !base_terms;
    false
  | Unsat -> true
  | Unknown -> assert false
  
let check_equality_BWZ (f1: formula) (f2: formula) : bool = 
  let open Bitwuzla_cxx in
  let options = Options.default () in
  Options.set options Produce_models true;
  let bitwuzla = Solver.create options in


  let bvterm_of_int (size: int) (v: int) : Term.t =
    mk_bv_value_int (mk_bv_sort size) v
  in

  let bvterm_of_ident (size: int) (id: ident) : Term.t = 
    mk_const (mk_bv_sort size) ~symbol:(id.id_symb ^ "#" ^ (string_of_int id.id_tag))
  in

  let size_of_bvtype ty = 
    match ty with 
    | `W s -> s
    | _ -> assert false
  in

  let base_terms : (ident, Term.t) Map.t ref = ref Map.empty in

  let rec doit (f: formula) : Term.t = 
    match f with
    | Base (id, t) -> 
      begin match Map.find_opt id !base_terms with
      | Some t -> t
      | None -> let t = bvterm_of_ident (size_of_bvtype t) id in
        base_terms := Map.add id t !base_terms;
        t
      end
    | Const (v, t) -> bvterm_of_int (size_of_bvtype t) v
    | Op (op, args) ->
      let args = List.map doit args in
      begin try begin match op, args with
      | `Extend (sz, true),  [bv] -> mk_term1_indexed1 Kind.Bv_sign_extend bv sz
      | `Extend (sz, false), [bv] -> mk_term1_indexed1 Kind.Bv_zero_extend bv sz
      | `Rem true,  [bv1; bv2] -> mk_term2 Kind.Bv_srem bv1 bv2
      | `Rem false, [bv1; bv2] -> mk_term2 Kind.Bv_urem bv1 bv2
      | `Div true , [bv1; bv2] -> mk_term2 Kind.Bv_sdiv bv1 bv2
      | `Div false, [bv1; bv2] -> mk_term2 Kind.Bv_udiv bv1 bv2 
      | `Add, [bv1; bv2] -> mk_term2 Kind.Bv_add bv1 bv2
      | `Shl, [bv1; bv2] -> mk_term2 Kind.Bv_shl bv1 bv2
      | `Shls, args -> assert false
      | `Lt true,  [bv1; bv2] -> mk_term2 Kind.Bv_slt bv1 bv2
      | `Lt false, [bv1; bv2] -> mk_term2 Kind.Bv_ult bv1 bv2
      | `ASliceSet, args -> assert false
      | `And, [bv1; bv2] -> mk_term2 Kind.Bv_and bv1 bv2
      | `Extract, args -> assert false
      | `Map, args -> assert false
      | `Ite, [c; t; f] -> assert false
      | `AInit, args -> assert false
      | `Sub, [bv1; bv2] -> mk_term2 Kind.Bv_sub bv1 bv2
      | `Ror, [bv1; bv2] -> mk_term2 Kind.Bv_ror bv1 bv2
      | `Get, args -> assert false
      | `Le true , [bv1; bv2] -> mk_term2 Kind.Bv_sle bv1 bv2
      | `Le false, [bv1; bv2] -> mk_term2 Kind.Bv_ule bv1 bv2
      | `Opp, [bv] -> mk_term1 Kind.Bv_neg bv
      | `Truncate sz, [bv] -> mk_term1_indexed2 Kind.Bv_extract bv (sz-1) 0
      | `Concat, [bv1; bv2] -> mk_term2 Kind.Bv_concat bv1 bv2
      | `Shrs (sz, true ), [bv1; bv2] -> 
        mk_term2 Kind.Bv_ashr bv1 (mk_term1_indexed1 Kind.Bv_zero_extend bv2 (sz - 8))
      | `Shrs (sz, false), [bv1; bv2] -> 
        mk_term2 Kind.Bv_shr bv1 (mk_term1_indexed1 Kind.Bv_zero_extend bv2 (sz - 8))
      | `Or, [bv1; bv2] -> mk_term2 Kind.Bv_or bv1 bv2
      | `Not, [bv] -> mk_term1 Kind.Bv_not bv
      | `Shr true , [bv1; bv2] -> mk_term2 Kind.Bv_ashr bv1 bv2
      | `Shr false, [bv1; bv2] -> mk_term2 Kind.Bv_shr bv1 bv2
      | `Xor, [bv1; bv2] -> mk_term2 Kind.Bv_xor bv1 bv2
      | `Insert, args -> assert false
      | `Init, args -> assert false
      | `Mul, [bv1; bv2] -> mk_term2 Kind.Bv_mul bv1 bv2
      | `Rol, [bv1; bv2] -> mk_term2 Kind.Bv_rol bv1 bv2
      | `A2B, args -> assert false
      | `ASliceGet, args -> assert false
      | `B2A, args -> assert false
      | `Eq, [bv1; bv2] -> mk_term2 Kind.Equal bv1 bv2
      | _ -> assert false
      end
    with e ->
      Format.eprintf "Failed on formula %a@." pp_formula f;
      raise e
    end
  in 
  let bv1 = doit f1 in
  let bv2 = doit f2 in
  Solver.assert_formula bitwuzla (mk_term2 Kind.Distinct bv1 bv2);
  let get_val (bv: Term.t) : Term.t =
    Solver.get_value bitwuzla bv
  in
  match Solver.check_sat bitwuzla with
  | Sat -> 
    Map.iter (fun _ t ->
      Format.eprintf "%a: %a@." Term.pp t Term.pp (get_val t)) !base_terms;
    false
  | Unsat -> true
  | Unknown -> assert false

let t_solve (tc: tcenv1) : tcenv =
  match (FApi.tc1_goal tc) with
  | f when f.f_ty = EcTypes.tbool -> 
    begin match EcFol.sform_of_form f with
(*
    | EcFol.SFeq (f1, f2) ->
      Format.eprintf "Checking equality@.";
      let bv1 = bvformula_of_form (FApi.tc1_hyps tc) f1 in
      let bv2 = bvformula_of_form (FApi.tc1_hyps tc) f2 in
      if check_equality_BWZ bv1 bv2 then
        Format.eprintf "Success@."
      else 
        Format.eprintf "Fail@.";
      assert false
*)
    | _ ->
      let f = bvformula_of_form (FApi.tc1_hyps tc) f in
      Format.eprintf "%a@." pp_formula f;
      if check_formula_BWZ f then
        Format.eprintf "Success@."
      else 
        Format.eprintf "Fail@.";
      assert false
    end
  | _ -> assert false

