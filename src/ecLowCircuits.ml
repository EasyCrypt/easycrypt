open EcBigInt
open EcUtils
open EcSymbols
open EcDecl
open EcIdent
open EcMemory

(* ==================================================================== *)
(* Backend bindings (lospecs) and library aliases *)
(* ==================================================================== *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

module CSMT = struct
  include Lospecs.Smt
end

module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Specifications
  type reg = node array
  type inp = int * int
  type model = (int * string) list

  let pp_node (fmt : Format.formatter) (n: node) = 
    Format.fprintf fmt "%a" (fun fmt -> Lospecs.Aig.pp_node fmt) n

  exception GetOutOfRange
  exception BadSlice of [`Get | `Set]

  let nodes_eq ({id=id1; _}: node) ({id=id2; _}: node) = id1 = id2
  let size_of_reg = Array.length

  let node_array_of_reg : reg -> node array = fun x -> x

  let node_list_of_reg : reg -> node list = fun x -> Array.to_list x 

  let reg_of_node_list : node list -> reg = fun x -> Array.of_list x

  let reg_of_node_array : node array -> reg = fun x -> x

  let reg_of_node : node -> reg = fun x -> [| x |]
  
  (* If this throws it is a programming error *)
  let node_of_reg : reg -> node = fun x -> x.(0)

  let reg_of_zint ~(size: int) (v: zint) : reg = 
    of_bigint_all ~size (to_zt v)

    

  let szint_of_reg (r: reg) : zint = 
    bools_of_reg r |> sbigint_of_bools |> of_zt 

  let uzint_of_reg (r: reg) : zint = 
    bools_of_reg r |> ubigint_of_bools |> of_zt
    
  let node_eq (n1: node) (n2: node) = xnor n1 n2
  let reg_eq (r1: reg) (r2: reg) =
    Array.fold (fun acc r ->
      and_ acc r)
      true_
      (Array.map2 node_eq r1 r2)
  let reg_ite (c: node) = Array.map2 (fun t f -> mux2 f t c) 

  let equiv ~(pcond: node) (r1: reg) (r2: reg) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    (CSMT.BWZ.equiv ctx r1 r2 pcond, lazy (CSMT.BWZ.model ctx))

  let sat (n: node) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    (CSMT.BWZ.sat ctx n, lazy (CSMT.BWZ.model ctx))

  let valid (n: node) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    (CSMT.BWZ.valid ctx n, lazy (CSMT.BWZ.model ctx))

  let slice (r: reg) (idx: int) (len: int) : reg =
    try Array.sub r idx len
    with Invalid_argument _ ->
      raise (BadSlice `Get)

  let subcirc (r: reg) (outs: int list) : reg =
    try 
      List.map (fun i -> r.(i)) outs |> Array.of_list
    with Invalid_argument _ ->
      raise (BadSlice `Get)

  let insert (r: reg) (idx: int) (r_in: reg) : reg =
    try
      let ret = Array.copy r in
      Array.blit r_in 0 ret idx (Array.length r_in);
      ret
    with Invalid_argument _ ->
      raise (BadSlice `Set)

  let get (r: reg) (idx: int) = 
    try 
      r.(idx)
    with Invalid_argument _ ->
      raise GetOutOfRange

  let permute (w: int) (perm: int -> int) (r: reg) : reg =
    Array.init (size_of_reg r) (fun i ->
      let block_idx, bit_idx = perm (i / w), (i mod w) in
      if block_idx < 0 then None 
      else
      let idx = block_idx*w + bit_idx in
      try
        Some r.(idx)
      with Invalid_argument _ ->
        raise GetOutOfRange
    ) |> Array.filter_map (fun x -> x)


  (* Node operations *)

  let input_of_size ?(offset = 0) ~id (i: int) = Array.init i (fun i -> input (id, offset + i))


  let applys (map_: inp -> node option) : reg -> reg =
    fun r -> Array.map (map map_) r


  (* SMTLib Base Ops *)
  let trunc (r1: reg) (size: int) : reg = Array.sub r1 0 size  
  let concat (r1: reg) (r2: reg) : reg = Array.append r1 r2 
  let flatten (rs: reg list) : reg = Array.concat rs
end

module CDeps = struct
  include Lospecs.Deps
    type dep = (int, int Set.t) Map.t
    type deps = dep array
    type block_deps = (int * dep) array

    let dep_of_node = fun n -> dep n
    let deps_of_reg = fun r -> deps r
    let block_deps_of_deps (w: int) (d: deps) : block_deps = 
      assert (Array.length d mod w = 0);
      Array.init (Array.length d / w) (fun i ->
        let deps = Array.sub d (i*w) w in
        let block = Array.fold_left (fun acc m ->
          Map.merge (fun _idx d1 d2 ->
            match d1, d2 with
            | None, None -> None
            | None, Some d | Some d, None -> Some d
            | Some d1, Some d2 -> Some (Set.union d1 d2)
          ) acc m) Map.empty deps in
        (w, block)
      )

    let block_deps_of_reg (w: int) (r: C.reg) : block_deps = 
      let deps = deps_of_reg r in
      block_deps_of_deps w deps

    let pp_dep (fmt: Format.formatter) (d: dep) : unit =
      Map.iter (fun id bits ->
          Format.fprintf fmt "%d: " id;
          Set.iter (fun bit -> Format.fprintf fmt "%d " bit) bits;
          Format.fprintf fmt "@\n"
        ) d

    let pp_deps (fmt: Format.formatter) (d: deps) : unit =
      Array.iteri (fun i d ->
        Format.fprintf fmt "@[<hov 2>[%d]:@\n%a@]@\n" i
        pp_dep d
      ) d
        
    let pp_block_deps (fmt: Format.formatter) (bd: block_deps) : unit =
      ignore @@ Array.fold_left (fun idx (w, d) ->
        Format.fprintf fmt "@[<hov 2>[%d..%d]:@\n%a@]@\n" idx (idx + w - 1)
        pp_dep d;
        idx + w
      ) 0 bd
    
    let dep_var_count (d: deps) : int = 
      Set.cardinal 
        (Array.fold_left (Set.union) Set.empty 
        (Array.map (fun dep -> Map.keys dep |> Set.of_enum) d)) 

    let merge_deps (d: deps) : dep =
      match Array.length d with
      | 0 -> Map.empty
      | _ -> Array.reduce (merge_deps) d

    (* Assumes single_dep, returns range (bot, top) such that valid idxs are bot <= i < top *)
    let dep_ranges (d: deps) : (int, int * int) Map.t =
      let d = merge_deps d in
      Map.map (fun ds -> (Set.min_elt_opt ds |> Option.default (-1), 
                          Set.max_elt_opt ds |> Option.default (-1))) d

    (* Checks that all dependencies of r are in the set inps *)
    (* Each elements of inps is (id, width) *)
    let check_inputs (r: C.reg) (inps: (int * int) list) : bool = 
      let ds = deps_of_reg r in
      Array.for_all (fun d -> 
        Map.for_all (fun id b ->
          match List.find_opt (fun (id_, _) -> id = id_) inps with
          | Some (_, b_) -> Set.for_all (fun b -> 0 <= b && b < b_) b
          | None -> false
        ) d
      ) ds 

    (* Checks if the first argument dependencies are contained in the second *)
    let dep_contained (subd: dep) (superd: dep) : bool =
      Map.for_all (fun id bits ->
        match Map.find_opt id superd with
        | None -> false
        | Some superbits -> Set.subset bits superbits
      ) subd

    let deps_equal (d1: dep) (d2: dep) : bool =
      (Map.equal (Set.equal) d1 d2)

    let deps_intersect (d1: dep) (d2: dep) : bool =
      not @@ Map.for_all (fun id bits1 ->
        match Map.find_opt id d2 with 
        | None -> true
        | Some bits2 -> Set.is_empty @@ Set.intersect bits1 bits2) d1

    let forall_inputs (check: int -> int -> bool) (r: C.reg) : bool =
      let d = deps_of_reg r in
      Array.for_all (fun d -> 
        Map.for_all (fun id bs -> Set.for_all (check id) bs) d) 
      d

    let rename_inputs (renamer: (int * int) -> (int * int) option) (r: C.reg) : C.reg =
      C.maps (fun (id, b) -> 
        Option.map (fun (id, b) -> C.input (id, b)) (renamer (id, b)) 
      ) r 

    let excise_bit ?renamings (n: C.node) : C.node * (int, int * int) Map.t =
      realign_inputs ?renamings n
end

(* ==================================================================== *)
(* Circuit interface, built directly on the lospecs backend.            *)
(* ==================================================================== *)
  (* -------------------------------------------------------------------- *)
  (* Module Types *)
  (* -------------------------------------------------------------------- *)
  type flatcirc = C.reg
  type ctype =
    CArray of {width: int; count: int; }
  | CBitstring of int
  | CTuple of ctype list
  type circ = {
    reg: flatcirc; 
    type_: ctype; 
}
  type cinp = {
    type_ : ctype;
    id   : int;
    name : string;  (* source-level name, for counter-model display *)
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun
  type model = C.model

  (* -------------------------------------------------------------------- *)
  (* Exceptions *)
  (* -------------------------------------------------------------------- *)
  type circconstructor = 
    | Slice of { slice_size: int; bitstring_size: int; offset: int }
    | SliceSet of { slice_size: int; bitstring_size: int; offset: int }
    | AGet of { container_size: int; index: int }
    | ASet of { container_size: int; index: int }
    | Get of { bitstring_size: int; index: int }
    | And 
    | Or
    | Ite   
    | Eq
    | Eqs
    

  type lowcircerror = 
  | MissingPVFromState 
  | CircInputUnificationFailure of (cinp * cinp) 
  | CircTyConversionFailure
  | CircConstructorInvalidArguments of circconstructor
  | CircComposeInvalidArguments 
  | CircComposeBadNumberOfArguments of { expected: int; received: int}
  | CircEquivNonBoolPCond
  | CircSmtNonBoolCirc
  | CircComputeBadNumberOfArguments of { expected: int; received: int}
  | CircComputeInvalidArguments of int
  | CloseWithoutLambda

  exception LowCircError of lowcircerror

  let lowcircerror (err: lowcircerror) =
    raise (LowCircError err)

 
  (* -------------------------------------------------------------------- *)
  (* Helper functions *)
  (* -------------------------------------------------------------------- *)

  let pp_flatcirc fmt fc = 
    let r = C.node_list_of_reg fc in
    List.iter (fun n ->
      Format.fprintf fmt "%a@." C.pp_node n
    ) r

  let circ_of_zint ~(size: int) (i: zint) : circ = 
    {reg = C.reg_of_zint ~size i; type_= CBitstring size }

  let circuit_of_zint ~(size: int) (i: zint) : circuit =
    ((circ_of_zint ~size i, []) :> circuit)

  (* Booleans are 1-bit bitstrings; [cbool] is the soft constructor for
     building such values (there is no distinct [CBool] constructor). *)
  let cbool : ctype = CBitstring 1

  let rec size_of_ctype (t: ctype) : int =
    match t with
    | CBitstring n -> n
    | CArray {width; count} -> width * count
    | CTuple tys -> List.sum (List.map size_of_ctype tys)

  (* -------------------------------------------------------------------- *)
  (* Pretty printers *)
  (* -------------------------------------------------------------------- *)
  let rec pp_ctype (fmt: Format.formatter) (t: ctype) : unit = 
    match t with
    | CArray {width; count}  -> Format.fprintf fmt "Array(%d@%d)" count width
    | CTuple szs -> Format.fprintf fmt "Tuple(%a)" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_ctype) szs
    | CBitstring w -> Format.fprintf fmt "Bitstring@%d" w

  let pp_cinp (fmt: Format.formatter) (inp: cinp) : unit = 
    Format.fprintf fmt "Input(id: %d, type = %a)" inp.id pp_ctype inp.type_

  let pp_circ (fmt : Format.formatter) (c: circ) : unit =
    Format.fprintf fmt "Circ(%a)" pp_ctype c.type_
    
  let pp_circuit (fmt: Format.formatter) ((c, inps) : circuit) : unit =
    Format.fprintf fmt "@[<hov 2>Circuit:@\nOut type %a@\nInputs: %a@]"
      pp_circ c
      (fun fmt inps -> List.iter (fun inp -> Format.fprintf fmt "%a@\n" pp_cinp inp) inps) inps
    
  (* arg for circuit construction *)
  (* -------------------------------------------------------------------- *)
  (* Arguments for circuit construction *)
  (* -------------------------------------------------------------------- *)
  module CArgs = struct
    type arg = 
    [ `Circuit of circuit
    | `Constant of zint   
    | `Init of int -> circuit 
    | `List of circuit list ]
    let arg_of_circuit c = 
      `Circuit c
    let arg_of_zint z =
      `Constant z
    let arg_of_circuits cs =
      `List cs
    let arg_of_init f =
      `Init f
    let pp_arg fmt arg : unit = 
      match arg with 
      | `Circuit  c  -> Format.fprintf fmt "%a" pp_circuit c 
      | `Constant i  -> Format.fprintf fmt "Constant: %s" (to_string i) 
      | `Init     f  -> Format.fprintf fmt "Init: Type of f(0): %a" pp_circuit (f 0) 
      | `List     cs -> Format.fprintf fmt "@[<hov 2> Circuit list: @\n%a@]" 
                          (fun fmt cs -> List.iter (Format.fprintf fmt "%a@\n" pp_circuit) cs) cs
  end
  open CArgs

  (* -------------------------------------------------------------------- *)
  (* Translation state *)
  (* -------------------------------------------------------------------- *)
  module TranslationState = struct
    type state = {
      circs    : circuit Mid.t;
      lambdas  : cinp list list; (* actually a stack *)
      pv_ids   : (ident * symbol, ident) Map.t; (* can be changed to int Msym.t if needed *)
      gstate   : EcGState.gstate;
    }

    let create_state (gstate : EcGState.gstate) : state = {
      circs = Mid.empty;
      lambdas = [];
      pv_ids = Map.empty; (* can be changed to int Msym.t if needed *)
      gstate;
    }

    (* Debug log through the gstate's registered notifiers. *)
    let log (st: state) (s: string) : unit =
      EcGState.notify `Debug (lazy s) st.gstate

    let update_state_pv (st: state) (m: memory) (s: symbol) (c: circuit) : state = 
      match Map.find_opt (m, s) st.pv_ids with
      | Some id -> {st with circs = Mid.add id c st.circs}
      | None -> let id = EcIdent.create s in
        { st with 
            pv_ids = Map.add (m, s) id st.pv_ids; 
            circs = Mid.add id c st.circs }

    let state_get_pv_opt (st: state) (m:memory) (s: symbol) : circuit option = 
      Option.bind (Map.find_opt (m, s) st.pv_ids) (fun id -> Mid.find_opt id st.circs) 

    let state_get_pv (st: state) (m: memory) (pv: symbol) : circuit = 
      match state_get_pv_opt st m pv with
      | Some circ -> circ
      | None -> lowcircerror (MissingPVFromState)

    let state_get_all_pv (st: state) : ((memory * symbol) * circuit) list = 
      let pvs = Map.bindings st.pv_ids in
      List.filter_map (fun (pv, id) -> match Mid.find_opt id st.circs with | None -> None | Some c -> Some (pv, c)) pvs 

    let state_get_all_memory (st: state) (m: memory) : (symbol * circuit) list = 
      List.filter_map (fun ((m_, s), c) -> if m = m_ then Some (s, c) else None) 
        (state_get_all_pv st)

    let update_state (st: state) (id: ident) (c: circuit) : state = 
      { st with circs = Mid.add id c st.circs }

    let state_get_opt (st: state) (id: ident) : circuit option = Mid.find_opt id st.circs 
    let state_get (st: state) (id: ident) : circuit = Mid.find id st.circs 
    let state_bindings (st: state) : (ident * circuit) list = Mid.bindings st.circs 
    let state_lambdas (st: state) : cinp list = st.lambdas |> List.rev |> List.flatten
    let state_is_closed (st: state) : bool = List.is_empty st.lambdas
    let state_close_circuit (st: state) ((c, inps): circuit) : circuit = 
      c, List.fold_left (fun inps lamb -> lamb @ inps) inps st.lambdas

    let map_state_var (f: (ident -> circuit -> circuit)) (st: state) : state = 
      {st with circs = Mid.mapi f st.circs}

    let cinput_of_type (name: [`Idn of ident | `Str of string]) (t: ctype) : cinp * circuit = 
      let name = match name with
      | `Idn id -> id
      | `Str s -> EcIdent.create s
      in
      { id = name.id_tag; type_ = t; name = EcIdent.name name},
      ({ reg = C.input_of_size ~id:name.id_tag (size_of_ctype t); type_ = t}, [])
        
    (* Circuit lambdas, for managing inputs *)
    let open_circ_lambda (st: state) (bnds: (ident  * ctype) list) : state = 
      let inps, cs = List.map (fun (id, t) -> 
        log st @@ Format.asprintf "Opening circuit lambda for ident: (%s, %d)@." (name id) (tag id);
        let inp, c = cinput_of_type (`Idn id) t
        in inp, (id, c)) bnds |> List.split in
      {st with
        lambdas = inps::st.lambdas;
        circs = List.fold_left (fun circs (id, c) -> Mid.add id c circs) st.circs cs }

    let open_circ_lambda_pv (st: state) (bnds : ((memory * symbol) * ctype) list) : state =
      let st, bnds = List.fold_left_map (fun st ((m, s), t) ->
        match Map.find_opt (m, s) st.pv_ids with
        | Some id -> st, (id, t) 
        | None -> let id = EcIdent.create s in
          { st with pv_ids = Map.add (m, s) id st.pv_ids}, (id, t)) st bnds
      in open_circ_lambda st bnds 

    let close_circ_lambda (st: state) : state = 
      match st.lambdas with
      | [] -> lowcircerror (CloseWithoutLambda)
      | inps::lambdas ->
        {st with lambdas = lambdas;
           circs = Mid.map (fun (c, cinps) -> (c, inps @ cinps)) st.circs }

    let circ_lambda_oneshot (st: state) (bnds : (ident * ctype) list) (c: state -> circuit) : circuit = 
      let st' = open_circ_lambda st bnds in
      let (c, inps) = c st' in
      (c, (List.hd st'.lambdas) @ inps)

  end

  (* Inputs helper functions *)
  let merge_inputs (cs: cinp list) (ds: cinp list) : cinp list =
(*     if List.for_all2 (fun {id=id1; type_=ct1} {id=id2; type_=ct2} -> id1 = id2 && ct1 = ct2) cs ds then cs  *)
    if cs = ds then cs 
    else cs @ ds

  let merge_inputs_list (cs: cinp list list) : cinp list =
    List.fold_right (merge_inputs) cs []

  let unify_inputs_renamer (target: cinp list) (inps: cinp list) : C.inp -> C.node option =
    let map = List.fold_left2 (fun map inp1 inp2 -> match inp1, inp2 with
      | {type_ = CBitstring w ; id=id_tgt},
        {type_ = CBitstring w'; id=id_orig} when w = w' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map) 
            map (List.init w (fun i -> i))
      | {type_ = CArray {width=w; count=n}; id=id_tgt},
        {type_ = CArray {width=w'; count=n'}; id=id_orig} when w = w' && n = n' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map) 
            map (List.init (w*n) (fun i -> i))
      | {type_ = CTuple tys ; id=id_tgt},
        {type_ = CTuple tys'; id=id_orig} when List.for_all2 (=) tys tys' -> 
          let w = List.sum (List.map size_of_ctype tys) in
          List.fold_left (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map) 
            map (List.init (w) (fun i -> i))
      | _ -> lowcircerror (CircInputUnificationFailure (inp1, inp2))
    ) Map.empty target inps in
    fun inp -> Map.find_opt inp map

  (* Renames circuit2 inputs to match circuit 1 *)
  let unify_inputs (target: cinp list) ((c, inps): circuit) : circ = 
    let map_ = unify_inputs_renamer target inps in
    {c with reg = C.applys map_ c.reg}

  let circuit_input_compatible ((c, _): circuit) (cinp: cinp) : bool =
    match c.type_, cinp with
    | CBitstring n, { type_ = CBitstring n' } when n = n' -> true
    | CArray {width=w; count=n}, { type_ = CArray {width=w'; count=n'}} when w = w' && n = n' -> true
    | CTuple (szs), { type_ = CTuple szs' } when List.all2 (=) szs szs' -> true
    | _ -> false

  (* Circuit tuples *)
  let circuit_tuple_proj ((c, inps): circuit) (i: int) =
    let r, tys = match c with
    | {reg = r; type_= CTuple tys} -> r, tys
    | _ -> assert false (* Programming error *)
    in
    let idx, ty = List.takedrop i tys in
    let ty = List.hd ty in
    let idx = List.fold_left (+) 0 (List.map size_of_ctype idx) in
    {reg = (C.slice r idx (size_of_ctype ty)); type_ = ty}, inps

  let circuit_tuple_of_circuits (cs: circuit list) : circuit = 
    let tys = (List.map (fun (c : circuit) -> (fst c).type_) cs) in 
    let circ = C.flatten (List.map (fun (c : circuit) -> (fst c).reg) cs) in 
    let inps = List.snd cs in
    {reg = circ; type_= CTuple tys}, merge_inputs_list inps

  let circuits_of_circuit_tuple ((c, tpinps) : circuit) : circuit list = 
    let tp, szs = match c with
    | {reg= tp; type_=CTuple szs} -> tp, szs
    | _ -> assert false (* Programming error *)
    in
    snd @@ List.fold_left_map 
      (fun idx ty -> 
        let sz = (size_of_ctype ty) in
        (idx + sz, 
        ({reg = (C.slice tp idx sz); type_ = ty}, tpinps)))
      0 szs 

  (* Convert a circuit's output to a given circuit type *)
  let convert_type (t: ctype) (({type_;_} as c, inps) as circ: circuit) : circuit = 
    if t = type_ then circ else begin 
      if (size_of_ctype t = size_of_ctype type_)
      then 
        {c with type_}, inps
      else 
        lowcircerror CircTyConversionFailure
    end
    
  let can_convert_input_type (t1: ctype) (t2: ctype) : bool =
    size_of_ctype t1 = size_of_ctype t2     

  let input_of_ctype ?(name : [`Str of string | `Idn of ident] = `Str "input") (ct: ctype) : circuit =
    let id, nm, c = match name with
    | `Str name -> let id = EcIdent.create name |> tag in
      id, name, C.input_of_size ~id (size_of_ctype ct)
    | `Idn idn -> let id = idn.id_tag in
      id, EcIdent.name idn, C.input_of_size ~id (size_of_ctype ct)
    in
    { reg = c; type_ = ct; }, [{ id; type_ = ct; name = nm }]

  let new_input_circuit ?(name = `Str "input") (ty: ctype) : circ * cinp = 
    let c, inps = input_of_ctype ~name ty in
    c, List.hd inps

  let circuit_true  = {reg = C.reg_of_node C.true_; type_ = cbool}, []
  let circuit_false  = {reg = C.reg_of_node C.false_; type_ = cbool}, []

  let circuit_and ((c, cinps): circuit) ((d, dinps): circuit) =  
    if c.type_ = d.type_ then
      { reg = C.land_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      lowcircerror @@ CircConstructorInvalidArguments And

  let circuit_or ((c, cinps): circuit) ((d, dinps): circuit) = 
    if c.type_ = d.type_ then
      { reg = C.lor_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      lowcircerror @@ CircConstructorInvalidArguments Or

  let circuit_not ((c, cinps): circuit) =
    {c with reg = C.lnot_ c.reg}, cinps

  let circuit_is_free (f: circuit) : bool = List.is_empty @@ snd f 

  let circuit_ite ~(c: circuit) ~(t: circuit) ~(f: circuit) : circuit =
    let inps = match c, t, f with
    | (_, []), (_, []), (_, []) -> []
    | _ -> assert false
    in
    let c = match (fst c).type_ with
    | CBitstring 1 -> C.node_of_reg (fst c).reg
    | _ -> assert false
    in
    let res_r = C.reg_ite c (fst t).reg (fst f).reg in
    match ((fst t).type_, (fst f).type_) with
    | CBitstring nt, CBitstring nf when nt = nf -> {reg = res_r; type_ = (fst t).type_}, inps
    | CArray {width=wt; count=nt}, CArray {width=wf; count=nf} when wt = wf && nt = nf -> {reg = res_r; type_ = (fst t).type_}, inps
    | CTuple szs_t, CTuple szs_f when List.all2 (=) szs_t szs_f -> {reg = res_r; type_ = (fst t).type_}, inps
    | _ -> lowcircerror @@ CircConstructorInvalidArguments Ite

  let circuit_eq (c: circuit) (d: circuit) : circuit =  
    match (fst c).type_, (fst d).type_ with
    | (CArray _), (CArray _)
    | (CTuple _), (CTuple _)
    | (CBitstring _), (CBitstring _) ->
      {reg = (C.reg_eq (fst c).reg (fst d).reg |> C.reg_of_node); type_ = cbool}, merge_inputs (snd c) (snd d)
    | _ -> lowcircerror @@ CircConstructorInvalidArguments Eq

  (* Ignore types, do extensionally over bits, return the circuits evaluating to the condition *)
  let circuit_eqs ((c, cinps): circuit) ((d, dinps): circuit) : circuit list = 
    let inps = merge_inputs cinps dinps in

    if (size_of_ctype c.type_ <> size_of_ctype d.type_) then 
      lowcircerror @@ CircConstructorInvalidArguments Eqs;

    let cs = C.node_list_of_reg c.reg in
    let ds = C.node_list_of_reg d.reg in
    List.map2 (fun c d ->
      let r = C.node_eq c d |> C.reg_of_node in
      {reg = r; type_ = cbool}, inps) cs ds

    
  let circuit_compose (c: circuit) (args: circuit list) : circuit = 
    begin try
      if not (List.for_all2 (fun c cinp -> circuit_input_compatible c cinp) args (snd c)) 
      then lowcircerror CircComposeInvalidArguments;
    with 
    | Invalid_argument _ -> lowcircerror @@ 
        CircComposeBadNumberOfArguments {
          expected = List.length (snd c);
          received = List.length args;
        }
    end;
    let map = List.fold_left2 (fun map {id} c -> Map.add id c map) Map.empty (snd c) (List.fst args) in
    let map_ (id, idx) = 
      let circ = Map.find_opt id map in
      Option.bind circ (fun c -> 
        match c.type_ with
        | CArray _ | CTuple _ | CBitstring _ ->
          begin try
            Some (C.get c.reg idx)
          with Invalid_argument _ -> None
          end
      )
    in
    
    let circ = {(fst c) with reg = C.applys map_ (fst c).reg} in
    let inps = merge_inputs_list (List.snd args) in
    (circ, inps)

  (* Fresh arbitrary value (used for [witness] and unknown values) *)
  let circuit_uninit (t: ctype) : circuit =
    let c, _ = input_of_ctype ~name:(`Str "uninit") t in
    c, []

  let circ_equiv ?(pcond:circuit option) ((c1, inps1): circuit) ((c2, inps2): circuit) : bool * C.model Lazy.t =
    let pcond = Option.map (convert_type cbool) pcond in (* Try to convert to bool *)
    let pcc = match pcond with
    | Some ({reg = b; type_ = CBitstring 1}, pcinps) ->
        C.map (unify_inputs_renamer inps1 pcinps) (C.node_of_reg b)
    | None -> C.true_
    | _ -> lowcircerror CircEquivNonBoolPCond
    in
    (* This throws, but we let it propagate upwards *)
    let c2 = unify_inputs inps1 (c2, inps2) in
    if (c1.type_ = c2.type_) then
      C.equiv ~pcond:pcc c1.reg c2.reg
    else (false, lazy [])

  let circ_sat ((c, _): circuit) : bool * C.model Lazy.t =
    let c = match c with
    | {type_ = CBitstring 1; reg} -> C.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
    in
    C.sat c

  let circ_valid ((c, _): circuit) : bool * C.model Lazy.t =
    let c = match c with
    | {type_ = CBitstring 1; reg} -> C.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
    in
    C.valid c

  (* Inputs mean different things depending on circuit type *)
  (* Allow unaligned slices *)
  let circuit_slice ~(size:int) ((c, inps): circuit) (offset: int) : circuit =
    try 
      {reg = C.slice c.reg offset size; type_ = CBitstring size}, inps
    with C.BadSlice `Get ->
      lowcircerror @@ CircConstructorInvalidArguments (Slice {
        slice_size = size;
        bitstring_size = C.size_of_reg c.reg;
        offset;
      })
    
  (* Slice by container index *)
  (* Does not type check *)
  let circuit_slice_insert ((orig_c, orig_inps): circuit) (idx: int) ((new_c, new_inps): circuit) : circuit = 
    try 
      { orig_c with reg = (C.insert orig_c.reg idx new_c.reg)}, merge_inputs orig_inps new_inps
    with C.BadSlice `Set ->
      lowcircerror @@ CircConstructorInvalidArguments (SliceSet {
        slice_size = C.size_of_reg new_c.reg;
        bitstring_size = C.size_of_reg orig_c.reg;
        offset = idx;
      })

  (* 
     Takes a circuit and uses dependency analysis to separate it into 
     subcircuits corresponding to the output bits
     
     In particular, equivalence between two circuits is equivalent 
     to equivalence between the subcircuits 

     Implicitly flattens everything to bitstrings
  *)
  let fillet_circuit ((c, inps) : circuit) : circuit list = 
    let r = c.reg |> C.node_list_of_reg in
    List.map (fun n ->
      let new_inps = List.map (fun {id=_;type_;name} ->
        {id=EcIdent.create "_" |> tag; type_; name}) inps
      in
      let renamings = List.combine 
        (List.map (fun {id} -> id) inps)
        (List.map (fun {id} -> id) new_inps)
      |> List.to_seq |> Map.of_seq 
      in
      let renamings = fun v -> Map.find_opt v renamings in
      let n', shifts = CDeps.excise_bit ~renamings n in

      let new_inps = List.filter_map (fun {id;name;_} ->
        match Map.find_opt id shifts with
        | Some (low, hi) -> Some {id; type_ = CBitstring (hi - low + 1); name}
        | None -> None
      ) new_inps in
      { reg = C.reg_of_node n';
        type_ = cbool },
      new_inps
    ) r

(*
  Correct order is:
  - Build two sided equality
  - Dependency collapse (into lanes)
    - Attach preconditions 
  - Realign inputs
  - Structural equality check
  - SMT check

*)
  (* Batches circuit checks by dependencies. Assumes equivalent checks are contiguous *)
  let batch_checks
    ?(sort = true)
    ?(mode : [`ByEq | `BySub] = `ByEq)
     (checks: circuit list) 
    : circuit list 
  =
    (* Order by dependencies *)
    let checks = if sort then begin 

    let checks = List.map (fun (c, inps) ->
      (c, inps), C.(CDeps.dep_of_node (node_of_reg c.reg))) checks in
    let checks = List.stable_sort (fun (_, d1) (_, d2) ->
      let m1 = (Map.keys d1 |> Set.of_enum |> Set.min_elt_opt) in 
      let m2 = (Map.keys d2 |> Set.of_enum |> Set.min_elt_opt) in 
      match m1, m2 with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some m1, Some m2 ->
      let c1 = Int.compare m1 m2 in
      if c1 = 0 then
        Int.compare (Map.find m1 d1 |> Set.min_elt_opt |> Option.default (-1)) (Map.find m1 d2 |> Set.min_elt_opt |> Option.default (-1))
      else
        c1
    ) checks in
    checks 
    end else
      List.map (fun c ->
        c, C.(CDeps.dep_of_node (node_of_reg (fst c).reg))) checks
    in

    let rec doit (acc: circuit list) (cur, d: circuit * CDeps.dep) (cs: (circuit * CDeps.dep) list) : circuit list =
      match cs with 
      | [] -> (cur::acc)
      | (c, d')::cs ->
        begin match mode with
          | `ByEq when CDeps.deps_equal d d' -> 
            doit acc ((circuit_and cur c), d) cs
          | `BySub when CDeps.(dep_contained d d') -> 
            doit acc ((circuit_and cur c), d') cs
          | `BySub when CDeps.(dep_contained d' d) ->
            doit acc ((circuit_and cur c), d) cs
          | _ ->
            doit (cur::acc) (c, d') cs
        end
    in

    match checks with
    | [] -> []
    | c::cs -> doit [] c cs

   
  let attach_compatible_pres ?(mode: [`Cont | `Eq | `Int] = `Cont) (pres: (circuit * CDeps.dep) list) ((post_circ, _) as post: circuit) : circuit =
    let d = C.(CDeps.dep_of_node (node_of_reg post_circ.reg)) in
    let compat_pres = List.filteri (fun _i (_c, pre_dep) ->
      match mode with
      | `Cont -> CDeps.dep_contained pre_dep d
      | `Eq -> CDeps.deps_equal pre_dep d
      | `Int -> CDeps.deps_intersect pre_dep d
    ) pres in
    let compat_pres = List.fst compat_pres in
    let pre = List.fold_left circuit_and circuit_true compat_pres in
    circuit_or (circuit_not pre) post

    let sublimate_inputs ((c, cinps): circuit) : circuit = 
    assert (c.type_ = cbool);
    let node_c = C.node_of_reg c.reg in
    let node_c, shifts = CDeps.excise_bit node_c in
    let inps = List.filter_map (fun {id; name; _} ->
      match Map.find_opt id shifts with
      | Some (low, hi) -> Some {id; type_ = CBitstring (hi - low + 1); name}
      | None -> None
    ) cinps in
    let c = C.reg_of_node node_c in
    { reg = c; type_ = cbool}, inps


  let collapse_lanes (lanes: circuit list) =
    (* Circuit structural equality after renaming *)
    let (===) (c1: circ) (c2: circ) : bool = 
      let n', _ = C.node_of_reg c1.reg |> CDeps.excise_bit in
      let n, _ = C.node_of_reg c2.reg |> CDeps.excise_bit in
      C.nodes_eq n n'
    in
    let rec collapse (acc: circuit list) (cur: circuit) (cs: circuit list) : circuit list = 
      match cs with
      | [] -> cur::acc
      | c::cs ->
        if (fst c) === (fst cur) then
          collapse acc cur cs
        else 
          collapse (cur::acc) c cs
    in
    let rec doit (cs: circuit list) : circuit list =
      match cs with
      | [] -> []
      | c::[] -> c::[]
      | c::cs -> begin try
        let idx, _ = List.findi (fun _ c2 -> (fst c) === (fst c2)) cs in
        let idx = idx + 1 in (* Length of the list to merge *)
        if idx = 1 then 
          doit (collapse [] c cs)
        else
          if (List.length (cs) + 1) mod idx != 0 then
            (c::cs)
          else
            let cs = List.chunkify idx (c::cs) |> List.map (List.reduce circuit_and) in
            doit cs
        with Not_found ->
          c::cs
      end
    in
    doit lanes

  (* 
    - Attaches preconditions to postconditions
    - Realigns inputs
    - Checks for structural equality of circuits
    - SMT check for any remainings ones
   *)
  let fillet_tauts (pres: circuit list) (posts: circuit list) : bool =
    (* Assumes everything is single bit outputs. *)
    let posts = List.filter_map (fun ((postc, _) as post) -> 
      if C.nodes_eq (C.node_of_reg postc.reg) C.true_ then None
      else Some post
    ) posts in
  
    match posts with
    | [] -> true
    | posts ->
      if (not (List.for_all (fun ({type_;reg=_}, _) -> type_ = cbool) pres))
      || (not (List.for_all (fun ({type_;reg=_}, _) -> type_ = cbool) posts)) then
        lowcircerror CircSmtNonBoolCirc;
      let pres = List.map (fun ((c, _) as circ) -> circ,
        CDeps.dep_of_node (C.node_of_reg c.reg)) pres in
      let posts = List.map (attach_compatible_pres ~mode:`Int pres) posts in
      let posts = collapse_lanes posts in

      List.map (fun post ->
        let post = sublimate_inputs post in
        fst (circ_valid post)) posts |>
      List.for_all identity
   
  let compute ~(sign: bool) ((r, inps) as c: circuit) (args: arg list) : zint option = 
    begin match r.type_ with
    | CBitstring _ -> ()
    | _ -> assert false 
    end;

    if List.compare_lengths args inps <> 0 
    then lowcircerror @@ CircComputeBadNumberOfArguments 
      { expected = List.length inps;
        received = List.length args; };

    let args = List.map2i (fun i arg inp ->
    match arg, inp with
    | `Circuit c, inp when circuit_input_compatible c inp -> c
    | `Constant i, {type_ = CBitstring size} -> { reg = (C.reg_of_zint ~size i); type_ = CBitstring size}, []
    | _ -> lowcircerror @@ CircComputeInvalidArguments i
    ) args inps 
    in
    match circuit_compose c args with
    | {reg = r; type_ = CBitstring _}, [] ->
      Some (if sign
        then C.szint_of_reg r
        else C.uzint_of_reg r)
    | _, _::_ -> assert false (* Should not happen *)
    | _ -> assert false (* Should not happen *)

  let circuit_aggregate (cs: circuit list) : circuit =
    let inps = List.snd cs in
    let cs = List.map (fun c -> (fst c).reg) cs in
    let c = C.flatten cs in
    let inps = merge_inputs_list inps in
    {reg = c; type_ = CBitstring (C.size_of_reg c)}, inps

  let input_aggregate_renamer (inps: cinp list) : cinp * (C.inp -> C.node option) =
    let new_id = create "aggregated" |> tag in
    let (size, map) = List.fold_left (fun (size, map) inp ->
      match inp with
      | { type_ = CBitstring w; id} ->
        (size + w, Map.add id (size, w) map) 
      | { type_ = CArray {width=w; count=n}; id} ->
        (size + (w*n), Map.add id (size, w*n) map)
      | { type_ = CTuple tys; id} ->
        let w = List.sum @@ List.map size_of_ctype tys in
        (size + w, Map.add id (size, w) map)
      ) (0, Map.empty) inps
    in
    {type_ = CBitstring size; id=new_id; name = "aggregated"},
    fun (id, bit) ->
      let base_sz = Map.find_opt id map in
      Option.bind base_sz (fun (base, sz) ->
        let idx = bit + base in
        if bit >= 0 && bit < sz then 
        Some (C.input (new_id, idx))
        else None
      ) 

  let circuit_aggregate_inputs ((c, inps): circuit) : circuit =
    let inp, renamer = input_aggregate_renamer inps in
    {c with reg = C.applys renamer c.reg}, [inp]

  let circuit_from_spec ?(name: symbol option) ((arg_tys, ret_ty) : (ctype list * ctype)) (spec: Lospecs.Ast.adef) : circuit = 
    let c args = C.circuit_of_specification args spec in

    let name = match name with 
    | Some name -> name ^ "_spec_input"
    | None -> "spec_input"
    in

    let cinps, inps = List.mapi (fun i ty ->
      let nm = name ^ "_" ^ (string_of_int i) in
      let id = EcIdent.create nm |> tag in
      let size : int = size_of_ctype ty in
      (C.input_of_size ~id size, { type_ = ty; id = id; name = nm } )
      ) arg_tys |> List.split in
    let c = c cinps in
    { reg = c; type_ = ret_ty}, inps 
(*     { reg = c; CBitstring c, inps) |> convert_type ret_ty *)

    (* -------------------------------------------------------------------- *)
    (* Bit-vector operators *)
    (* -------------------------------------------------------------------- *)
    module BVOps = struct
      let bvget (c: circuit) (i: int) : circuit = 
        match c with 
        | {reg; type_ = CBitstring n}, inps when 0 <= i && i < n -> 
          begin try
            {reg = C.reg_of_node (C.get reg i); type_ = cbool}, inps
          with C.GetOutOfRange ->
            lowcircerror (CircConstructorInvalidArguments (Get {
              bitstring_size = n;
              index = i;
            }))
          end
        | _ -> assert false (* programming error *)

      let circuit_of_parametric_bvop (op: EcDecl.crb_bvoperator) (args: arg list) : circuit =
      match op with 
      | { kind = `ASliceGet (((_, Some _), (_, Some _)), (_, Some m)) } -> 
        begin match args with 
        (* Assume type checking from EC? *)
        | [ `Circuit (({type_ = CArray _}, _) as circ) ; `Constant i ] ->
          begin
            match (fst circ).type_ with
            | CArray {width=w'; count=n'} -> 
              circuit_slice ~size:m ({reg = (fst circ).reg; type_ = CBitstring (w' * n')}, (snd circ)) (to_int i)
            | _ -> assert false (* Does not happen, guarded by match above *)
          end
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `ASliceSet (((_, Some _), (_, Some _)), (_, Some _)) } -> 
        begin match args with 
        | [ `Circuit (({type_ = CArray _}, _) as arr_circ) ; `Constant i ; `Circuit (({type_ = CBitstring _}, _) as bs_circ) ] ->
          begin match (fst arr_circ).type_, (fst bs_circ).type_ with
          | CArray _, CBitstring _ ->
            circuit_slice_insert arr_circ (to_int i) bs_circ 

          (* If this fails, then we have an inconsistent binding, should be prevented by EC *)
          | _ -> assert false 
        end 
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end

      | { kind = `Extract ((_, Some _), (_, Some w_out), aligned) } -> 
        begin match args with
        | [ `Circuit (({type_ = CBitstring _}, _ ) as c) ; `Constant i ] ->
          circuit_slice ~size:w_out c ((if aligned then w_out else 1) * to_int i)
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `Insert ((_, Some _), (_, Some _)) } -> 
        begin match args with
        | [ `Circuit (({type_ = CBitstring _}, _) as orig_c) ; `Constant i ; `Circuit (({ type_=CBitstring _}, _) as new_c) ] ->
            (circuit_slice_insert orig_c (to_int i) new_c :> circuit)
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end

      | { kind = `Map ((_, Some w_i), (_, Some w_o), (_, Some n)) } -> 
        begin match args with 
        | [ `Circuit cf; `Circuit ({reg = arr; type_ = CArray {width=_; count=_}}, _) ] ->
          let circs, inps = List.split @@ List.map (fun c -> 
            match circuit_compose cf [c] with
            | { type_ = CBitstring _; reg}, inps -> reg, inps 
            | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
            ) 
          (List.init n (fun i -> {reg = (C.slice arr (i*w_i) w_i); type_ = CBitstring w_i}, []))
          in
          (* Inputs of all components should match after map *)
          if not (List.for_all ((=) (List.hd inps)) inps) then 
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let inps = List.hd inps in
          let circ = { reg = (C.flatten circs); type_ = CArray {width=w_o; count=n}} in  
          (circ, inps) 
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `Get (_, Some _) } -> 
        begin match args with
        | [ `Circuit c; `Constant i ] -> bvget c (EcBigInt.to_int i)
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `AInit ((_, Some n), (_, Some w_o)) } -> 
        begin match args with
        | [ `Init init_f ] -> 
          let circs, cinps = List.split @@ List.init n init_f in
          let circs = List.map 
            (function 
              | {type_ = CBitstring _; reg = r} when C.size_of_reg r = w_o -> r 
            (* Invalid type for init component *)
            | _ -> assert false) (* Should be caught by EC typechecking + binding correctness *) 
          circs in
          (* Inputs should be uniform across components after mapping *)
          if not (List.for_all ((=) (List.hd cinps)) cinps) then
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let cinps = List.hd cinps in
          {type_ = CArray {width=w_o; count=n} ; reg = C.flatten circs}, cinps 
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `Init (_, Some w) } -> 
        begin match args with 
        | [ `Init init_f ] ->
          let circs, cinps = List.split @@ List.init w init_f in
          let circs = List.map 
            (function 
            | {type_ = CBitstring 1; reg = b} -> C.node_of_reg b
            (* Return type should be bool (= bit) for components *)
            | _ -> assert false) (* Should be caught by EC typechecking + binding correctness *)
            circs
          in
          if not (List.for_all ((=) (List.hd cinps)) cinps) then
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let cinps = List.hd cinps in
          {type_ = CBitstring w; reg = (C.reg_of_node_list circs)}, cinps
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | _ -> assert false (* Should not happen because calls should be guarded by call to op_is_parametric_bvop *)


      let circuit_of_bvop (op: EcDecl.crb_bvoperator) : circuit = 
      match op with
      | { kind = `Add (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.add_dropc c1 c2 )}, [inp1; inp2] 

      | { kind = `Sub (_, Some size) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.sub_dropc c1 c2)}, [inp1; inp2] 

      | { kind = `Mul  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.umull c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.udiv c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.sdiv c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.umod c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.smod c1 c2)}, [inp1; inp2] 

      | { kind = `Shl  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.shift ~side:`L ~sign:`L c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.shift ~side:`R ~sign:`L c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.shift ~side:`R ~sign:`A c1 c2)}, [inp1; inp2] 

      | { kind = `Shls  ((_, Some size1), (_, Some size2)) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (C.shift ~side:`L ~sign:`L c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (C.shift ~side:`R ~sign:`L c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (C.shift ~side:`R ~sign:`A c1 c2)}, [inp1; inp2] 

      | { kind = `Rol  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.rol c1 c2)}, [inp1; inp2] 

      | { kind = `Ror  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.ror c1 c2)}, [inp1; inp2] 

      | { kind = `And  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.land_ c1 c2)}, [inp1; inp2] 

      | { kind = `Or   (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.lor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Xor  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (C.lxor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Not  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring size; reg = (C.lnot_ c1)}, [inp1] 

      | { kind = `Opp  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring size; reg = (C.opp c1)}, [inp1] 

      | { kind = `Lt ((_, Some size), false) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = cbool; reg = C.reg_of_node (C.ult c1 c2)}, [inp1; inp2] 
      
      | { kind = `Lt ((_, Some size), true) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = cbool; reg = C.reg_of_node (C.slt c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), false) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = cbool; reg = C.reg_of_node (C.ule c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), true) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = cbool; reg = C.reg_of_node (C.sle c1 c2)}, [inp1; inp2] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), false) } ->
        (* assert (size <= out_size); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring out_size; reg = (C.uextend ~size:out_size c1)}, [inp1] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), true) } ->
        (* assert (size <= out_size); *)  
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring out_size; reg = (C.sextend ~size:out_size c1)}, [inp1] 

      | { kind = `Truncate ((_, Some size), (_, Some out_sz)) } ->
        (* assert (size >= out_sz); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring out_sz; reg = (C.trunc c1 out_sz)}, [inp1] 

      | { kind = `Concat ((_, Some sz1), (_, Some sz2), (_, Some szo)) } ->
        (* assert (sz1 + sz2 = szo); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring sz1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring sz2) in
        {type_ = CBitstring szo; reg = (C.concat c1 c2)}, [inp1; inp2] 

      | { kind = `A2B (((_, Some w), (_, Some n)), (_, Some m))} ->
        (* assert (n * w = m); *)
        let c, inp = new_input_circuit (CArray {width=w;count=n}) in  
        {c with type_ = CBitstring m}, [inp] 

      | { kind = `B2A ((_, Some m), ((_, Some w), (_, Some n)))} ->
        (* assert (n * w = m); *)
        let c, inp = new_input_circuit (CBitstring m) in
        {c with type_ = CArray {width=w; count=n}}, [inp] 

      | { kind = `ASliceGet _ | `ASliceSet _ | `Extract _ | `Insert _ | `Map _ | `AInit _ | `Get _ | `Init _  } 
      | _ 
        -> assert false (* Should be guarded by call to op_is_bvop *)
    end

    (* -------------------------------------------------------------------- *)
    (* Array operators *)
    (* -------------------------------------------------------------------- *)
    module ArrayOps = struct
      let array_get (c: circuit) (i: int) : circuit = 
        match c with 
        | ({reg = c; type_ = CArray {width=w; count=n}}, inps) -> 
          begin try
            { type_ = CBitstring w; reg = (C.slice c (i*w) w)}, inps  
          with C.BadSlice `Get ->
            lowcircerror @@ CircConstructorInvalidArguments (AGet {
              container_size = n;
              index = i;
            }) end
        | _ -> assert false (* Programming error *)

      let array_set (a: circuit) (pos: int) (bs: circuit) : circuit =
        match a, bs with 
        | (({reg = arr; type_ =  CArray {width=w; count=n}}, inps) : circuit), (({reg = bs; type_ = CBitstring w'}, cinps): circuit) -> 
          begin try
            assert (w = w');
            { type_ = CArray {width=w; count=n}; reg = (C.insert arr (pos * w) bs)},
            merge_inputs inps cinps
          with C.BadSlice `Set -> 
            lowcircerror @@ CircConstructorInvalidArguments (ASet {
              container_size = n;
              index = pos;
            })
          end
        | _ -> assert false (* Programming error *)

      let array_oflist (circs : circuit list) (dfl: circuit) (len: int) : circuit =
        let circs, inps = List.split circs in
        let dif = len - List.length circs in assert (dif >= 0);
        let circs = circs @ (List.init dif (fun _ -> fst dfl)) in
        let inps = if dif > 0 then inps @ [snd dfl] else inps in
        let circs = List.map 
          (function 
            | {type_ = CBitstring _; reg = r} -> r
            | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
          ) circs
        in
        { type_ = CArray {width=C.size_of_reg (List.hd circs); count=len}; reg = (C.flatten circs)}, merge_inputs_list inps 
    end
include CArgs
include TranslationState
include BVOps
include ArrayOps

let reset_backend_state () =
  C.HCons.clear ()
