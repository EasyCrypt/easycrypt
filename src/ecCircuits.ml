(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcParsetree
open EcEnv
open EcAst
open EcCoreFol
open EcIdent

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

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

(* -------------------------------------------------------------------- *)
type width = int

(* FIXME: make inps be variables *)
type circuit = {
  circ: C.reg;
  inps: (ident * int) list
}

let inputs_equal (f: circuit) (g: circuit) : bool = 
  (List.compare_lengths f.inps g.inps = 0) && 
  (List.for_all2 (=) (List.snd f.inps) (List.snd g.inps))

(* -------------------------------------------------------------------- *)
(* ?? *)
let circ_dep_split (r : C.reg) : C.reg list =
  let deps = C.deps r in

  List.fold_left_map (fun acc ((lo, hi), _) ->
    swap (List.split_nth (hi - lo + 1) acc)
  ) r deps |> snd


(* ------------------------------------------------------------------------------- *)
(* -------------------------------------------------------------------- *)
exception BDepError

module BaseOps = struct
  let temp_symbol = "temp_circ_input"
  
  let is_baseop (p: path) : bool = 
    match (EcPath.toqsymbol p) with
    | ["Top"; "JWord"; _], _ -> true

    (* AdHoc for barrett FIXME: remove later *)
    | _, "sext16_32" -> true
    | _, "uext16_32" -> true
    | _, "sar_32_26" -> true
    | _, "truncate32_16" -> true
    | _, "eqmod64q" -> true
    
    | _ -> false

  let circuit_of_baseop (p: path) : circuit = 
    match (EcPath.toqsymbol p) with
    | (["Top"; "JWord"; sz], op) as qpath -> 
      let size = match sz with
      | "W256" -> 256
      | "W128" -> 128 
      | "W64" -> 64 
      | "W32" -> 32 
      | "W16" -> 16 
      | "W8" -> 8 
      | _ -> Format.eprintf "Unknown size for path %s@." (EcSymbols.string_of_qsymbol qpath); assert false
      in 

    begin match op with
    (* Arithmetic: *)
    | "+" ->
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = C.add_dropc c1 c2; inps = [(id1, size); (id2, size)]}

    | "*" -> (* Unsigned low word mul *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = C.umull c1 c2; inps = [(id1, size); (id2, size)]}

    | "[-]" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = C.opp c1; inps = [(id1, size)]}


    (* Comparisons: *)
    | "\\ule" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = [C.uge c2 c1]; inps=[(id1, size); (id2, size)]}
    | "\\ult" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = [C.ugt c2 c1]; inps=[(id1, size); (id2, size)]}
    
    (* Conversions *)
    | "of_int" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = c1; inps = [(id1, 256)]} (* FIXME: Assumes integeres are 256 bits *)

    
    | _ -> Format.eprintf "Unregistered JOp : %s @." (EcSymbols.string_of_qsymbol qpath); assert false
    end
  (* AdHoc stuff for barrett example FIXME: remove later *)
  | _, "sext16_32" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    {circ = C.sextend ~size:32 c1; inps = [(id1, 16)]}

    | _, "uext16_32" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    {circ = C.uextend ~size:32 c1; inps = [(id1, 16)]}
  
  | _, "sar_32_26" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:32 ~name:id1.id_tag in
    {circ = C.arshift ~offset:26 c1; inps = [(id1, 32)]}

  | _, "truncate32_16" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    { circ = c1; inps=[(id1, 32)]}

  | _, "eqmod64q" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:16 ~name:id2.id_tag in
    let q = C.of_int ~size:16 3329 in
    let dc = C.sub_dropc c1 c2 in
    (* let dc = C.smod dc q in *)
    (* let dc = C.ugt (C.of_int ~size:16 1) dc in *)
    let dp_modq = C.rem dc q in
    let dm_modq = C.rem (C.opp dc) q in
    let dp_modqt = C.ugt (C.of_int ~size:16 1) dp_modq in
    let dm_modqt = C.ugt (C.of_int ~size:16 1) dm_modq in
    {circ = [C.or_ dp_modqt dm_modqt]; inps = [(id1, 16); (id2, 16)]}
  
  | _ -> assert false
end

(* -------------------------------------------------------------------- *)
(* Basis for hardcoded circuit gen *)
let circuit_from_spec (env: env) (p : path) : C.reg list -> C.reg  =
  (* | "OPP_8" -> C.opp (args |> registers_of_bargs env |> List.hd) (* FIXME: Needs to be in spec *) *)
  match EcEnv.Circ.lookup_circuit_path env p with
  | Some op -> C.func_from_spec op
  | None -> Format.eprintf "No operator for path: %s@."
    (let a,b = EcPath.toqsymbol p in List.fold_right (fun a b -> a ^ "." ^ b) a b);
    assert false 


let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circ.lookup_bitstring_size env t with
  | Some w -> w
  | None -> Format.eprintf "No bitvector binding for type %a@."
  (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t; raise BDepError

let apply (c: C.reg) (idn: ident) (v: C.reg) : C.reg = 
  let map_ = fun (id, i) -> 
    if id = tag idn then List.nth_opt v i
    else None
  in C.maps map_ c

let applys (c: C.reg) (vs: (ident * C.reg) list) : C.reg =
  let map_ = fun (id, i) -> 
    let vo = List.find_opt (fun (idn, _) -> id = tag idn) vs in
    let vo = Option.map snd vo in
    Option.bind vo (fun v -> List.nth_opt v i)
  in C.maps map_ c

(* FIXME: check in what order to put the args *)
let apply_args (c: circuit) (vs: circuit list) : circuit = 
  assert (List.compare_lengths c.inps vs >= 0);
  let new_circs, new_inps = List.map (fun c -> (c.circ, c.inps)) vs |> List.split in
  let apply_inps, old_inps = List.takedrop (List.length vs) c.inps in
  
  let () =
  try
    assert (List.for_all2 (fun a b -> (snd a) = List.length b) apply_inps new_circs)
  with
  | Assert_failure _ -> Format.eprintf "Apply arg size mismatch: ";
    List.iter2 (fun a b -> Format.eprintf "(%d, %d) " (snd a) (List.length b)) apply_inps new_circs;
    assert false
  in

  (* Tentative : *)
  let new_inps = List.flatten new_inps |> List.unique_hash in
  
  let new_c = applys c.circ (List.map2 (fun a b -> (fst a, b)) apply_inps new_circs) in
  {circ = new_c; inps = new_inps @ old_inps}

let apply_args_strict (c: circuit) (vs: circuit list) : circuit =
  assert (List.compare_lengths c.inps vs = 0);
  apply_args c vs

let apply_arg (c: circuit) (v: C.reg) : circuit =
  match c.inps with
  | (idn, w)::inps ->
    begin try 
      assert (List.length v = w);
      { circ = apply c.circ idn v; inps }
    with 
    | Assert_failure _ -> 
      Format.eprintf "Input width %d does not match argument width %d@." (List.length v) w;
      raise BDepError 
    end
  | [] -> Format.eprintf "Can't apply to circuit with no arguments@."; raise BDepError


let circ_equiv (f: circuit) (g: circuit) (pcond: circuit) : bool = 
  let module B = (val HL.makeBWZinterface ()) in
  inputs_equal f g &&
  inputs_equal f pcond &&
  begin
    let new_inps = List.mapi (fun i (_, w) -> 
      let id = EcIdent.create ("equiv_inp_" ^ (string_of_int i)) in
      {circ = C.reg ~size:w ~name:id.id_tag; inps = [(id, w)]}) f.inps in
    let f2 = apply_args f new_inps in
    let g2 = apply_args g new_inps in
    let pcond2 = apply_args pcond new_inps in
    B.circ_equiv f2.circ g2.circ (List.hd pcond2.circ)
  end
  
let circ_check (f: circuit) : bool =
  assert (List.length f.circ = 1);
  let module B = (val HL.makeBWZinterface ()) in
  B.circ_taut (List.hd f.circ)

let circ_sat (f: circuit) : bool = 
  assert (List.length f.circ = 1);
  let module B = (val HL.makeBWZinterface ()) in
  B.circ_sat (List.hd f.circ)

(* Vars = bindings in scope (maybe we have some other way of doing this? *)

let circuit_of_form ?(pstate : (symbol, circuit) Map.t = Map.empty) (env: env) (f : EcAst.form) : circuit =
  let vars : (ident * int) list = [] in
  let cache : (ident, circuit) Map.t = Map.empty in
  
  let rec doit (cache: (ident, circuit) Map.t) (vars: (ident * int) list) (env: env) (f: form) :  _ * circuit = 
    match f.f_node with
    (* hardcoding size for now FIXME *)
    | Fint z -> env, {circ = C.of_bigint ~size:256 (to_zt z); inps = []}
      (* failwith "Add logic to deal with ints (maybe force conversion?)" *)
      (* hlenv, C.of_bigint ~size:256 (EcAst.BI.to_zt z) *)
    | Fif (c_f, t_f, f_f) -> 
        let env, c_c = doit cache vars env c_f in
        let env, t_c = doit cache vars env t_f in
        let env, f_c = doit cache vars env f_f in
        let () = assert (List.length c_c.circ = 1) in
        let c_c = List.hd c_c.circ in
        env, {
        circ = C.mux2_reg f_c.circ t_c.circ c_c;
        inps = List.rev vars; }
      (* Assumes no quantifier bindings/new inputs within if *)
    (* hardcoding size for now FIXME *)
    | Flocal idn -> 
      begin match Map.find_opt idn cache with
      | Some circ -> env, circ
      | None -> try 
        let sz = width_of_type env f.f_ty in
        assert (List.find (fun a -> (fst a) = idn) vars |> snd = sz);
        env, 
        { circ = C.reg ~size:sz ~name:idn.id_tag;
          inps = [(idn, sz)];
        }
        with
        | Assert_failure _ -> 
          Format.eprintf "Var binding size %d for %s does not match size of form type %d@."
          (List.find (fun a -> (fst a) = idn) vars |> snd) idn.id_symb (width_of_type env f.f_ty);
           raise BDepError
        | Not_found -> Format.eprintf "Var binding not found for %s@." idn.id_symb; raise BDepError
      end
        (* HL.reg hlenv ~size:(width_of_type env f.f_ty) ~name:idn.id_symb *) 
        (* TODO: Check name after *)
    | Fop (pth, _) -> 
      if BaseOps.is_baseop pth then
        env, BaseOps.circuit_of_baseop pth
      else
        let f = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper ( Some (OP_Plain (f, _))) -> f
        | _ -> failwith "Unsupported op kind"
        in doit cache vars env f
      (* (hlenv, nullary pth) *)

    | Fapp _ -> 
      (* Check processing order of args and f FIXME *)
      let (f, fs) = EcCoreFol.destr_app f in
      let env, f_c = doit cache vars env f in
      let env, fcs = List.fold_left_map
        (doit cache vars)
        env fs 
      in
      env, apply_args f_c fcs
      
    | Fquant (qnt, binds, f) -> 
      begin match qnt with
      (* FIXME: check if this is desired behaviour for exists and add logic for others *)
      | Lexists -> failwith "NOT IMPLEMENTED: Existential quantifiers "
      | Llambda | Lforall -> 
        let vars = List.fold_left (fun m (idn, t) -> (idn, (width_of_type env (gty_as_ty t)))::m) vars binds in
        doit cache vars env f
      end
    | Fproj (f, i) ->
        begin match f.f_node with
        | Ftuple tp ->
          doit cache vars env (tp |> List.drop (i-1) |> List.hd)
        | _ -> failwith "Don't handle projections on non-tuples"
        end
    | Fmatch  (f, fs, ty) -> assert false
    | Flet    (lpat, v, f) -> 
      begin match lpat with
      | LSymbol (idn, ty) -> let env, vc = doit cache vars env v in
        let cache = Map.add idn vc cache in
        doit cache vars env f
      | LTuple  symbs -> assert false
      | LRecord (pth, osymbs) -> assert false
      end
    | Fpvar   (pv, mem) -> 
      let v = match pv with
      | PVloc v -> v
      | _ -> failwith "No global vars yet"
      in
      let res = match Map.find_opt v pstate with
        | Some circ -> circ
        | None -> failwith ("No value for var " ^ v)
      in env, res
    | Fglob   (id, mem) -> assert false
    | Ftuple  comps -> assert false
    | _ -> failwith "Not yet implemented"
  in 
  let env, f_c = doit cache vars env f in
  f_c


let circuit_of_path (env: env) (p: path) : circuit =
  let f = EcEnv.Op.by_path p env in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type"
  in
  circuit_of_form env f

    
(* -------------------------------------------------------------------- *)
(* WIP *)
let process_op (env : env) (f: pqsymbol) (f2: pqsymbol) : unit = 
  let f = EcEnv.Op.lookup f.pl_desc env |> snd in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let fc = circuit_of_form env f in

  let f2 = EcEnv.Op.lookup f2.pl_desc env |> snd in
  let f2 = match f2.op_kind with
  | OB_oper (Some (OP_Plain (f, _))) -> f
  | _ -> failwith "Invalid operator type" in
  let fc2 = circuit_of_form env f2 in

  (* let fc = List.take 4 fc in (* FIXME: this needs to be removed *) *)
  (* let () = Format.eprintf "%a" (HL.pp_node hlenv) (List.hd fc) in *)
  (* DEBUG PRINTS FOR OP CIRCUIT *)
  let namer = fun id -> 
    List.find_opt (fun inp -> tag (fst inp) = id) fc.inps 
    |> Option.map fst |> Option.map name |> Option.default (string_of_int id) in
  let () = Format.eprintf "Out len: %d @." (List.length fc.circ) in
  let () = HL.inputs_of_reg fc.circ |> Set.to_list |> List.iter (fun x -> Format.eprintf "%s %d@." (fst x |> namer) (snd x)) in
  let () = Format.eprintf "%a@." (fun fmt -> HL.pp_deps ~namer fmt) (HL.deps fc.circ |> Array.to_list) in
  let () = Format.eprintf "Args for circuit: "; 
            List.iter (fun (idn, w) -> Format.eprintf "(%s, %d) " idn.id_symb w) fc.inps;
            Format.eprintf "@." in
  Format.eprintf "Circuits: %s@." (if circ_equiv fc fc2 {circ=[C.true_];inps=fc.inps} then "Equiv" else "Not equiv")
