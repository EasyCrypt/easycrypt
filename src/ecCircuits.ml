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
type deps = ((int * int) * int C.VarRange.t) list

(* FIXME: make inps be variables *)
type circuit = {
  circ: C.reg;
  inps: (ident * int) list
}

(* Maybe rename to sig_equals? *)
let inputs_equal (f: circuit) (g: circuit) : bool = 
  (List.compare_lengths f.inps g.inps = 0) && 
  (List.for_all2 (=) (List.snd f.inps) (List.snd g.inps))

let merge_inps (f: circuit) (g: circuit) : (circuit * circuit) option =
  let f_inps = Map.of_seq (List.to_seq f.inps) in
  let g_inps = Map.of_seq (List.to_seq g.inps) in
  try 
    let ret  = Map.union_stdlib (fun k a b -> assert (a = b); Some a) f_inps g_inps in
    let inps = Map.to_seq ret |> List.of_seq in
    Some ({f with inps = inps}, {g with inps = inps})
  with 
  | Assert_failure _ -> None

let merge_inps3 (f: circuit) (g: circuit) (pcond: circuit) : (circuit * circuit * circuit) option =
  let f_inps = Map.of_seq (List.to_seq f.inps) in
  let g_inps = Map.of_seq (List.to_seq g.inps) in
  let pcond_inps = Map.of_seq (List.to_seq pcond.inps) in
  try 
    let ret  = Map.union_stdlib (fun k a b -> assert (a = b); Some a) f_inps g_inps in
    let ret  = Map.union_stdlib (fun k a b -> assert (a = b); Some a) ret pcond_inps in
    let inps = Map.to_seq ret |> List.of_seq in
    Some ({f with inps}, {g with inps}, {pcond with inps})
  with 
  | Assert_failure _ -> None

let inputs_consistent (f: circuit) (g:circuit) : bool = 
  Option.is_some (merge_inps f g)
    
(* -------------------------------------------------------------------- *)
exception CircError of string

let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circ.lookup_bitstring_size env t with
  | Some w -> w
  | None -> let err = Format.asprintf "No bitvector binding for type %a@."
  (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in 
  raise (CircError err)

let circuit_aggregate (c: circuit list) : circuit =
  try
    assert (List.for_all (fun circ -> circ.inps = (List.hd c).inps) c);
    {circ = List.flatten (List.map (fun circ -> circ.circ) c); inps=(List.hd c).inps}
  with
    | Assert_failure _ -> 
      let err = Format.asprintf "Bad circuit inputs: @." ^
      (List.reduce (^) @@ List.map (fun c -> List.reduce (^) @@ List.map
      (fun (id, w) -> Format.asprintf "((%d, %s), %d) " id.id_tag id.id_symb w) c.inps) c) ^
      "\n" in
      raise @@ CircError err

(* Concatenates two circuits and their inputs 
   Strict mode: input variables must be the same, sizes are concat
   Non-strict : input variables may be different, coinciding ones
                are concat, order is first arg inps then second
*)
(* NON-TESTED FIXME *)
let circuit_merge ?(strict=true) (c: circuit) (d: circuit) : circuit =
  let inps = List.map 
    (fun (id, w) -> 
    let w2 = List.find_opt (fun v -> (fst v)=id) d.inps 
      |> Option.map snd |> Option.default 0 in (id, w + w2)
    ) c.inps in
  let inps = inps @ (List.filter (fun (id, w) -> List.mem id (List.fst inps)) d.inps) in
  {circ=c.circ @ d.circ; inps}

let circuit_concat ?(n:int option) (c: circuit list) : circuit =
  let temp_name = "concat_input" in
  let () = match n with
  | None -> ()
  | Some n -> assert (List.for_all (fun c -> List.for_all (fun a -> snd a = n) c.inps) c)
  in
  let size = List.fold_left (fun acc c -> List.fold_left (+) acc (List.snd c.inps)) 0 c in
  let id = create temp_name in
  (* let new_inp = C.reg ~size ~name:id.id_tag in *)
  let old_inps = List.map (fun c -> c.inps) c |> List.flatten in
  let map_, sz = List.fold_left (fun (map_, i) (id_, w) -> 
    List.init w (fun j -> ((id_.id_tag, j), C.input (id.id_tag, i+j))) |>
    List.fold_left (fun map_ (k, v) -> Map.add k v map_) map_, i+w
  ) (Map.empty, 0) old_inps in
  assert (size = sz); (* Probably superfluous *)
  let map_ = fun x -> Map.find_opt x map_ in
  let circ = List.flatten @@ List.map (fun c -> c.circ) c in
  let circ = C.maps map_ circ in
  {circ; inps=[(id,size)]}

let input_of_tdep (n: int) (bs: int Set.t) : _ * (ident * int) = 
  let temp_symbol = "tdep_ident" in
  let m = Set.cardinal bs in
  let id = create temp_symbol in
  let map_ = Set.to_seq bs |> List.of_seq in
  let map_ = List.map (fun a -> (n, a)) map_ in
  let map_ = List.combine map_ (List.init m (fun i -> C.input (id.id_tag, i))) in
  let map_ = Map.of_seq (List.to_seq map_) in
  map_, (id, m)
  
let inputs_of_tdep (td: HL.tdeps) :  _ * (ident * int) list =
  Map.foldi (fun n bs (map_, inps) -> let map_2, inp = input_of_tdep n bs in
    (Map.union map_ map_2, inp::inps)) td (Map.empty, [])   

  

(* This takes a circuit with big output and input and returns the split one *)
let circuit_block_split (in_size: int) (out_size: int) (c: circuit) : circuit list =
  let deps = HL.deps c.circ in
  let bdeps = HL.split_deps out_size deps in
  assert (List.for_all (HL.check_dep_width in_size) (List.snd bdeps));
  assert ((List.fold_left (+) 0 (List.snd c.inps)) mod in_size = 0);

  let doit (db: HL.tdblock) (c: C.reg) : circuit * C.reg =
    let res, c = List.takedrop (fst db) c in
    let map_, inps = inputs_of_tdep (snd db) in
    let res = C.maps (fun a -> Map.find_opt a map_) res in
    {circ = res; inps}, c
  in
  let cs, c = List.fold_left (fun (cs, c) bd -> let r, c = doit bd c in
    (r::cs, c)) ([],c.circ) bdeps in
  assert (List.length c = 0);
  cs

(* -------------------------------------------------------------------- *)
(* Basis for hardcoded circuit gen *)
let circuit_from_spec_ (env: env) (p : path) : C.reg list -> C.reg  =
  (* | "OPP_8" -> C.opp (args |> registers_of_bargs env |> List.hd) (* FIXME: Needs to be in spec *) *)
  match EcEnv.Circ.lookup_circuit_path env p with
  | Some op -> C.func_from_spec op
  | None -> Format.eprintf "No operator for path: %s@."
    (let a,b = EcPath.toqsymbol p in List.fold_right (fun a b -> a ^ "." ^ b) a b);
    assert false 



let circuit_from_spec (env: env) (p : path) : circuit = 
  let temp_name = "spec_input" in
  let circ = circuit_from_spec_ env p in
  let op = EcEnv.Op.by_path p env in

  let rec unroll_fty_rev (acc: ty list) (ty: ty) : ty list =
    try 
      let a, b = EcTypes.tfrom_tfun2 ty in
      (unroll_fty_rev (a::acc) b)
    with
    | Assert_failure _ -> ty::acc
  in

  let argtys = unroll_fty_rev [] op.op_ty |> List.tl |> List.rev in
  let cinps, inps = List.map (fun ty -> 
    let id = EcIdent.create temp_name in
    let size = width_of_type env ty in
    (C.reg ~name:id.id_tag ~size, (id, size))
    ) argtys|> List.split in
  {circ = circ cinps; inps}
    
  
module BaseOps = struct
  let temp_symbol = "temp_circ_input"
  
  let is_baseop (env: env) (p: path) : bool = 
    match (EcPath.toqsymbol p) with
    | ["Top"; "JWord"; _], _ -> true
    | ["Top"; "JModel_x86"], _ -> true

    (* AdHoc for barrett FIXME: remove later *)
    | _, "sext16_32" -> true
    | _, "uext16_32" -> true
    | _, "sar_32_26" -> true
    | _, "truncate32_16" -> true
    | _, "eqmod64q" -> true
    | _, "bvueq" -> true
    | _, "bvseq" -> true
    | _, "/\\" -> true
    | _, "&&" -> true
    | _, "\\/" -> true
    | _, "||" -> true
    | _, "[!]" -> true
    | _, "=>" -> true
    | _, "<=>" -> true
    | _, "true" -> true
    | _, "false" -> true
    
    | _ -> begin match EcEnv.Circ.lookup_qfabvop_path env p with
      | Some _ -> Format.eprintf "Found qfabv binding for %s@." (EcPath.tostring p); true
      | None   -> Format.eprintf "Did not find qfabv binding for %s@." (EcPath.tostring p); false
    end

  let circuit_of_baseop (env: env) (p: path) : circuit = 
    match (EcPath.toqsymbol p) with
    | (["Top"; "JWord"; sz], op) as qpath when op <> "+" -> 
      let size = match sz with
      | "W256" -> 256
      | "W128" -> 128 
      | "W64" -> 64 
      | "W32" -> 32 
      | "W16" -> 16 
      | "W8" -> 8 
      | "W16u16" -> 256
      | _ -> Format.eprintf "Unknown size for path %s@." (EcSymbols.string_of_qsymbol qpath); assert false
      in 

    begin match op with
    (* Arithmetic: *)
    (* | "+" -> *)
      (* let id1 = EcIdent.create (temp_symbol) in *)
      (* let id2 = EcIdent.create (temp_symbol) in *)
      (* let c1 = C.reg ~size ~name:id1.id_tag in *)
      (* let c2 = C.reg ~size ~name:id2.id_tag in *)
      (* {circ = C.add_dropc c1 c2; inps = [(id1, size); (id2, size)]} *)

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

    (* Bitwise operations *)
    | "andw" -> (* Unsigned low word mul *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = C.land_ c1 c2; inps = [(id1, size); (id2, size)]}

    | "`>>`" -> (* Unsigned low word mul *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size:8 ~name:id2.id_tag in
      {circ = C.shift ~side:`R ~sign:`L c1 c2; inps = [(id1, size); (id2, 8)]}

    | "`<<`" -> (* Unsigned low word mul *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size:8 ~name:id2.id_tag in
      {circ = C.shift ~side:`L ~sign:`L c1 c2; inps = [(id1, size); (id2, 8)]}


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
    (* Comparisons: *)
    | "\\sle" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = [C.sge c2 c1]; inps=[(id1, size); (id2, size)]}
    | "\\slt" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = [C.sgt c2 c1]; inps=[(id1, size); (id2, size)]}
    
    (* Conversions *)
    | "of_int" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = c1; inps = [(id1, 256)]} (* FIXME: Assumes integeres are 256 bits *)
    
    | "to_uint" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = C.uextend ~size:256 c1; inps = [(id1, size)]} (* FIXME: Assumes integeres are 256 bits *)

    
    | _ -> 
      let err = Format.asprintf "Unregistered JOp : %s @." (EcSymbols.string_of_qsymbol qpath) in
      raise @@ CircError err
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

  
  | _, "bvueq" -> (* FIXME: remove hardcoded size *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:16 ~name:id2.id_tag in
    {circ = [C.bvueq c1 c2]; inps = [(id1, 16); (id2, 16)]}
  
  | _, "bvseq" -> (* FIXME: remove hardcoded size *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:32 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:32 ~name:id2.id_tag in
    {circ = [C.bvseq c1 c2]; inps = [(id1, 32); (id2, 32)]}

  
  | _,"[!]" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    {circ = C.lnot_ c1; inps = [(id1, 1)]}

  | _, "&&"
  | _, "/\\" -> (* FIXME: remove hardcoded size *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = C.land_ c1 c2; inps = [(id1, 1); (id2, 1)]}

  | _, "\\/"
  | _, "||" -> (* FIXME: remove hardcoded size *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = C.lor_ c1 c2; inps = [(id1, 1); (id2, 1)]}

  | _, "=>" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = C.lor_ (C.lnot_ c1) c2; inps = [(id1, 1); (id2, 1)]}
  
  | _, "<=>" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = C.lxnor_ c1 c2; inps = [(id1, 1); (id2, 1)]}
    
  | _, "true" ->
    {circ = [C.true_]; inps = []}

  | _, "false" ->
    {circ = [C.false_]; inps = []}

  | _, "eqmod64q" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:16 ~name:id2.id_tag in
    let c1 = C.sextend ~size:64 c1 in
    let c2 = C.sextend ~size:64 c2 in
    let q = C.of_int ~size:64 3329 in
    let c1 = C.smod c1 q in
    let c2 = C.smod c2 q in
    let dc = C.sub_dropc c1 c2 in
    (* let dc = C.smod dc q in *)
    let dc = C.ugt (C.of_int ~size:64 1) dc in
    (* let dp_modq = C.urem dc q in *)
    (* let dm_modq = C.urem (C.opp dc) q in *)
    (* let dp_modqt = C.ugt (C.of_int ~size:16 1) dp_modq in *)
    (* let dm_modqt = C.ugt (C.of_int ~size:16 1) dm_modq in *)
    (* let dc = C.or_ dp_modqt dm_modqt in *)
    {circ = [dc]; inps = [(id1, 16); (id2, 16)]}
  
  | _ -> begin match EcEnv.Circ.lookup_qfabvop_path env p with
    | Some BVADD size -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = C.add_dropc c1 c2; inps = [(id1, size); (id2, size)]}
    | Some BVSUB size ->
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = C.sub_dropc c1 c2; inps = [(id1, size); (id2, size)]}
    | _ -> raise @@ CircError "Failed to generate op"
    end
end

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
  (* Format.eprintf "#Args: %d@." (List.length vs); *)
  (* List.iter (fun (a,b) -> Format.eprintf "%s@%d@." a.id_symb b) c.inps; *)
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
      let err = Format.asprintf "Input width %d does not match argument width %d@." (List.length v) w in
      raise @@ CircError err
    end
  | [] -> let err = Format.asprintf "Can't apply to circuit with no arguments@." in
     raise @@ CircError err

(* FIXME: arranjar renamings *)
(* TODO: figure out how to deal with circuits with different inputs or some that match *)
let circ_equiv (f: circuit) (g: circuit) (pcond: circuit option) : bool = 
  let pcond = match pcond with
  | Some pcond -> pcond
  | None -> {circ = [C.true_]; inps = f.inps}
  in
  List.iter (fun (a,b) -> Format.eprintf "f: %s@%d@." a.id_symb b) f.inps;
  List.iter (fun (a,b) -> Format.eprintf "g: %s@%d@." a.id_symb b) g.inps;
  List.iter (fun (a,b) -> Format.eprintf "p: %s@%d@." a.id_symb b) pcond.inps;
  (* inputs_equal f g && *)
  (* inputs_equal f pcond && *)
  (* let cs = merge_inps3 f g pcond in *)
  (* Option.is_some cs && *) 
  let g = {g with inps = g.inps @ (List.drop (List.length g.inps) f.inps)} in
  let pcond = {pcond with inps = pcond.inps @ (List.drop (List.length pcond.inps) f.inps)} in
  begin
    (* let f, g, pcond = cs |> Option.get in *)
    (* let f, pcond = merge_inps f pcond |> Option.get in *)
    let new_inps = List.mapi (fun i (_, w) -> 
      let id = EcIdent.create ("equiv_inp_" ^ (string_of_int i)) in
      {circ = C.reg ~size:w ~name:id.id_tag; inps = [(id, w)]}) f.inps in
    (* let new_inps = List.map (fun (id, w) -> *)
      (* {circ = C.reg ~size:w ~name:id.id_tag; inps = [(id, w)]}) f.inps in *)
    let f2 = apply_args f new_inps in
    let g2 = apply_args g new_inps in
    let pcond2 = apply_args pcond new_inps in
    (List.for_all2 (==) f.circ g2.circ) ||
    let module B = (val HL.makeBWZinterface ()) in
    B.circ_equiv f2.circ g2.circ (List.hd pcond2.circ) (List.map (fun (a,b) -> (a.id_tag, b)) f.inps)
  end
  
let circ_check (f: circuit) (pcond: circuit option) : bool =
  assert (List.length f.circ = 1);
  let module B = (val HL.makeBWZinterface ()) in
  let f = match f with
  | {circ=[f]; _} -> f
  | _ -> raise @@ CircError "Form should only output one bit (bool)"
  in
  match pcond with
  | None -> B.circ_taut f
  | Some {circ=[pcond];_} -> not @@ B.circ_sat @@ (C.and_ pcond (C.neg f))
  | _ -> raise @@ CircError "Precondition should output one bit (bool)"

let circ_sat (f: circuit) (pcond: circuit option): bool = 
  assert (List.length f.circ = 1);
  let module B = (val HL.makeBWZinterface ()) in
  let f = match f with
  | {circ=[f]; _} -> f
  | _ -> raise @@ CircError "Form should only output one bit (bool)"
  in
  match pcond with
  | Some {circ=[pcond]; _} -> B.circ_sat (C.and_ pcond f)
  | None -> B.circ_sat f
  | _ -> raise @@ CircError "pcond should only output one bit (bool)"
  

(* Vars = bindings in scope (maybe we have some other way of doing this? *)

(* Refactor this later *)
let op_cache = ref Mp.empty

(* TODO: simplify args and unify dealing with cache / vars *)
let circuit_of_form ?(pstate : (symbol, circuit) Map.t = Map.empty) ?(cache=Map.empty)(env: env) (f : EcAst.form) : circuit =
  let vars : (ident * int) list = [] in
  let cache : (ident, circuit) Map.t = cache in
  
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
        (* TODO: change this to ite c_c t_c f_c *)
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
          let err = Format.asprintf "Var binding size %d for %s does not match size of form type %d@."
          (List.find (fun a -> (fst a) = idn) vars |> snd) idn.id_symb (width_of_type env f.f_ty) in
           raise @@ CircError err
        | Not_found -> let err = Format.asprintf "Var binding not found for %s@." idn.id_symb in 
          raise @@ CircError err
      end
        (* HL.reg hlenv ~size:(width_of_type env f.f_ty) ~name:idn.id_symb *) 
        (* TODO: Check name after *)
    | Fop (pth, _) -> 
      begin
      match Mp.find_opt pth !op_cache with
      | Some op -> 
        (* Format.eprintf "Using cached op: %s@." (EcPath.tostring pth); *)
        env, op
      | None -> 
        (* Format.eprintf "No cache for op: %s@." (EcPath.tostring pth); *)
      if BaseOps.is_baseop env pth then
        try
          let circ = BaseOps.circuit_of_baseop env pth in
          op_cache := Mp.add pth circ !op_cache;
          env, circ 
        with
        | CircError err -> 
          let circ = circuit_from_spec env pth in
          op_cache := Mp.add pth circ !op_cache;
          env, circ
      else
        let f = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper ( Some (OP_Plain (f, _))) -> f
        | _ -> Format.eprintf "%s@." (EcPath.tostring pth); failwith "Unsupported op kind"
        in 
        let env, circ = doit cache vars env f in
        op_cache := Mp.add pth circ !op_cache;
        env, circ
    end
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

let input_of_variable (env:env) (v: variable) : circuit =
  let size = width_of_type env v.v_type in
  let inp = (create v.v_name, size) in
  let c = C.reg ~size ~name:(fst inp).id_tag in
  {circ = c; inps=[inp]}
  

let pstate_of_memtype ?(pstate = Map.empty) (env: env) (mt: memtype) =
  let inps = match mt with
  | Lmt_concrete (Some lmt) -> lmt.lmt_decl 
    |> List.filter_map (fun ov -> if Option.is_none ov.ov_name then None
                                  else Some {v_name = Option.get ov.ov_name; v_type=ov.ov_type})
  | _ -> assert false
  in

  let inps = List.map (input_of_variable env) inps in
  let pstate = List.fold_left 
    (fun pstate inp -> Map.add (List.hd inp.inps |> fst).id_symb inp pstate)
    pstate inps 
  in pstate


let process_instr (env:env) (mem: memory) ?(cache: _ = Map.empty) (pstate: _) (inst: instr) =
    try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, ty), e) -> Map.add v (form_of_expr mem e |> circuit_of_form ~pstate ~cache env) pstate
    | _ -> failwith "Case not implemented yet"
    with 
    | e -> let err = Format.asprintf "BDep failed on instr: %a@.Exception thrown: %s@."
        (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst
        (Printexc.to_string e) in 
        raise @@ CircError err

let insts_equiv (env: env) ((mem, mt): memenv) ?(pstate: _ = Map.empty) (insts_left: instr list) (insts_right: instr list): bool =
  let pstate = pstate_of_memtype ~pstate env mt in
  let pstate_left = List.fold_left (process_instr env mem) pstate insts_left in
  let pstate_right = List.fold_left (process_instr env mem) pstate insts_right in
  (* Maybe this not needed? *)

  (* if (Map.keys pstate_left |> Set.of_enum) != (Map.keys pstate_right |> Set.of_enum) then *)
    (* begin *)
    (* Format.eprintf "Left: @."; *)
    (* Map.iter (fun k _ -> Format.eprintf "%s@." k) pstate_left; *)
    (* Format.eprintf "Right: @."; *)
    (* Map.iter (fun k _ -> Format.eprintf "%s@." k) pstate_right; *)
    (* false *)
    (* end *)
  (* else *)
    Map.foldi (fun var circ bacc -> bacc && (circ_equiv circ (Map.find var pstate_right) None)) pstate_left true
    
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
  Format.eprintf "Circuits: %s@." (if circ_equiv fc fc2 None then "Equiv" else "Not equiv")
