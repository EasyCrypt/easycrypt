open EcBigInt
open EcUtils
open EcSymbols
open EcDecl
open EcIdent
open EcMemory

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_spec
end

module CDeps = struct
  include Lospecs.Deps
end

module CSMT = struct
  include Lospecs.Smt
end

module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

let debug : bool = false

(* Backend implementing minimal functions needed for the translation *)
(* Minimal expected functionality is QF_ABV *)
(* Input are: some identifier + some bit *)
module type CBackend = sig
  type node (* Corresponds to a single output node *)
  type reg
  (* Id + offset, both assumed starting at 0 *)
  type inp = int * int

  val pp_node : Format.formatter -> node -> unit

  exception NonConstantCircuit (* FIXME: Rename later *)
  exception GetOutOfRange (* FIXME: Do we even need this? *)
  exception BadSlice of [`Get | `Set]

  val true_ : node
  val false_ : node

  val nodes_eq : node -> node -> bool

  val bad : node
  val bad_reg : int -> reg 
  val has_bad : node -> bool
  val have_bad : reg -> int option

  val node_array_of_reg : reg -> node array
  val node_list_of_reg : reg -> node list
  val reg_of_node_list : node list -> reg
  val reg_of_node_array : node array -> reg
  val reg_of_node : node -> reg
  val node_of_reg : reg -> node 

  val input_node : id:int -> int -> node
  val input_of_size : ?offset:int -> id:int -> int -> reg

  val reg_of_zint : size:int -> zint -> reg
  val bool_array_of_reg : reg -> bool array
  val bool_list_of_reg : reg -> bool list
  val szint_of_reg : reg -> zint
  val uzint_of_reg : reg -> zint
  val size_of_reg : reg -> int

  val apply : (inp -> node option) -> node -> node
  val applys : (inp -> node option) -> reg -> reg
  val circuit_from_spec : Lospecs.Ast.adef -> reg list -> reg 
  val equiv : ?inps:inp list -> pcond:node -> reg -> reg -> bool
  val sat : ?inps:inp list -> node -> bool 
  val taut : ?inps:inp list -> node -> bool 

  val slice : reg -> int -> int -> reg
  val subcirc : reg -> (int list) -> reg
  val insert : reg -> int -> reg -> reg
  val get : reg -> int -> node
  val permute : int -> (int -> int) -> reg -> reg

  val node_eq : node -> node -> node
  val reg_eq : reg -> reg -> node
  val node_ite : node -> node -> node -> node
  val reg_ite : node -> reg -> reg -> reg

  val band : node -> node -> node
  val bor : node -> node -> node
  val bxor : node -> node -> node
  val bnot : node -> node
  val bxnor : node -> node -> node
  val bnand : node -> node -> node
  val bnor : node -> node -> node

  (* SMTLib Base Operations *)
  (* FIXME: decide if boolean ops are going to be defined 
     on registers or on nodes *)
  val add : reg -> reg -> reg
  val sub : reg -> reg -> reg
  val opp : reg -> reg
  val mul : reg -> reg -> reg
  val udiv : reg -> reg -> reg
  val sdiv : reg -> reg -> reg
  val umod : reg -> reg -> reg (* FIXME: mod or rem here? *)
  val smod : reg -> reg -> reg
  val lshl : reg -> reg -> reg
  val lshr : reg -> reg -> reg
  val ashr : reg -> reg -> reg
  val rol : reg -> reg -> reg
  val ror : reg -> reg -> reg
  val land_ : reg -> reg -> reg
  val lor_ : reg -> reg -> reg
  val lxor_ : reg -> reg -> reg
  val lnot_ : reg -> reg 
  val ult: reg -> reg -> node
  val slt : reg -> reg -> node
  val ule : reg -> reg -> node
  val sle : reg -> reg -> node
  val uext : reg -> int -> reg
  val sext : reg -> int -> reg
  val trunc : reg -> int -> reg
  val concat : reg -> reg -> reg

  val flatten : reg list -> reg

  val reg_to_file : input_count:int -> ?inp_name_map:(int -> string) -> name:string -> reg -> symbol 

  module Deps : sig
    type dep = (int, int Set.t) Map.t
    type deps = dep array
    type block_deps

    val dep_of_node : node -> dep
    val deps_of_reg : reg -> deps
    val block_deps_of_deps : int -> deps -> block_deps 
    val block_deps_of_reg : int -> reg -> block_deps

    val pp_dep : Format.formatter -> dep -> unit
    val pp_deps : Format.formatter -> deps -> unit
    val pp_block_deps : Format.formatter -> block_deps -> unit

    val dep_var_count : deps -> int
    (* Assumes single_dep *)
    val dep_ranges : deps -> (int, int * int) Map.t
    (* Checks if first dep is a subset of second dep *) 
    val dep_contained : dep -> dep -> bool
    (* Checks if two dep sets are equal *)
    val deps_equal : dep -> dep -> bool
    (* Checks if two dep sets intersect *)
    val deps_intersect : dep -> dep -> bool
    (* Checks if all the deps are in a given list of inputs *)
    val check_inputs : reg -> (int * int) list -> bool

    val forall_inputs : (int -> int -> bool) -> reg -> bool
    val rename_inputs : ((int * int) -> (int * int) option) -> reg -> reg
    (* TODO: Rename *)
    val excise_bit : ?renamings:(int -> int option) -> node -> node * (int, int * int) Map.t
  end
end

module LospecsBack : CBackend = struct
  type node = C.node
  type reg = C.node array
  type inp = int * int

  let pp_node (fmt : Format.formatter) (n: node) = 
    Format.fprintf fmt "%a" (fun fmt -> Lospecs.Aig.pp_node fmt) n

  exception NonConstantCircuit (* FIXME: Rename later *)
  exception GetOutOfRange (* FIXME: Do we even need this? *)
  exception BadSlice of [`Get | `Set]

  let true_ = C.true_
  let false_ = C.false_
  let nodes_eq ({id=id1; _}: node) ({id=id2; _}: node) = id1 = id2
  let size_of_reg = Array.length
  let bad = C.input (-1, -1)
  let bad_reg = fun i -> Array.make i bad
  let has_bad : node -> bool = 
    let cache : (int, bool) Hashtbl.t = Hashtbl.create 0 in
    let rec doit (n: node) : bool =
      match Hashtbl.find_option cache (Int.abs n.id) with
      | Some b -> b
      | None -> let b = doit_r n.gate in
        Hashtbl.add cache (Int.abs n.id) b;
        b
    and doit_r (n: C.node_r) : bool =
      match n with
      | C.Input (-1, -1) -> true
      | C.Input _
      | C.False -> false
      | C.And (n1, n2) -> (doit n1) || (doit n2)
    in
    fun b -> doit b

  let have_bad (r: reg) : int option =
    Array.find_opt (fun (_, r) -> has_bad r) (Array.mapi (fun i r -> (i,r)) r) |> Option.map fst

  let node_array_of_reg : reg -> node array = fun x -> x

  let node_list_of_reg : reg -> node list = fun x -> Array.to_list x 

  let reg_of_node_list : node list -> reg = fun x -> Array.of_list x

  let reg_of_node_array : node array -> reg = fun x -> x

  let reg_of_node : node -> reg = fun x -> [| x |]
  
  (* If this throws it is a programming error *)
  let node_of_reg : reg -> node = fun x -> x.(0)

  let reg_of_zint ~(size: int) (v: zint) : reg = 
    C.of_bigint_all ~size (to_zt v)

  let bool_array_of_reg (r: reg) : bool array = 
    C.bools_of_reg r
    
  let bool_list_of_reg (r: reg) =
    C.bool_list_of_reg r

  let szint_of_reg (r: reg) : zint = 
    C.bools_of_reg r |> C.sbigint_of_bools |> of_zt 

  let uzint_of_reg (r: reg) : zint = 
    C.bools_of_reg r |> C.ubigint_of_bools |> of_zt
    
  let node_eq (n1: node) (n2: node) = C.xnor n1 n2
  let reg_eq (r1: reg) (r2: reg) = 
    Array.fold (fun acc r ->
      C.and_ acc r)
      C.true_
      (Array.map2 node_eq r1 r2)
  let node_ite (c: node) (t: node) (f: node) = C.mux2 f t c 
  let reg_ite (c: node) = Array.map2 (node_ite c) 

  let equiv ?(inps: inp list option) ~(pcond: node) (r1: reg) (r2: reg) : bool = 
    let open CSMT in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_equiv ?inps r1 r2 pcond  

  let sat ?(inps: inp list option) (n: node) : bool =
    let open CSMT in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_sat ?inps n 

  let taut ?(inps: inp list option) (n: node) : bool =
    let open CSMT in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_taut ?inps n 

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
  let band : node -> node -> node = C.and_
  let bor : node -> node -> node = C.or_
  let bxor : node -> node -> node = C.xor
  let bnot : node -> node = C.neg
  let bxnor : node -> node -> node = C.xnor
  let bnand : node -> node -> node = C.nand
  let bnor : node -> node -> node = fun n1 n2 -> C.neg @@ C.or_ n1 n2 

  let input_node ~id i = C.input (id, i)
  let input_of_size ?(offset = 0) ~id (i: int) = Array.init i (fun i -> C.input (id, offset + i))

  let apply (map_: inp -> node option) (n: node) : node= 
    C.map map_ n

  let applys (map_: inp -> node option) : reg -> reg =
    fun r -> Array.map (C.map map_) r

  let circuit_from_spec (def: Lospecs.Ast.adef) (args: reg list) : reg = 
    C.circuit_of_specification args def

  (* SMTLib Base Ops *)
  let add (r1: reg) (r2: reg) : reg = C.add_dropc r1 r2 
  let sub (r1: reg) (r2: reg) : reg = C.sub_dropc r1 r2 
  let opp (r: reg) : reg = C.opp r 
  let mul (r1: reg) (r2: reg) : reg = C.umull r1 r2 
  let udiv (r1: reg) (r2: reg) : reg = C.udiv r1 r2 
  let sdiv (r1: reg) (r2: reg) : reg = C.sdiv r1 r2 
  (* FIXME: mod or rem here? *)
  let umod (r1: reg) (r2: reg) : reg  = C.umod r1 r2 
  let smod (r1: reg) (r2: reg) : reg = C.smod r1 r2 
  let lshl (r1: reg) (r2: reg) : reg = C.shift ~side:`L ~sign:`L r1 r2 
  let lshr (r1: reg) (r2: reg) : reg = C.shift ~side:`R ~sign:`L  r1 r2 
  let ashr (r1: reg) (r2: reg) : reg = C.shift ~side:`R ~sign:`A  r1 r2 
  let rol (r1: reg) (r2: reg) : reg = C.rol r1 r2 
  let ror (r1: reg) (r2: reg) : reg = C.ror r1 r2 
  let land_ (r1: reg) (r2: reg) : reg = C.land_ r1 r2 
  let lor_ (r1: reg) (r2: reg) : reg = C.lor_ r1 r2 
  let lxor_ (r1: reg) (r2: reg) : reg = C.lxor_ r1 r2 
  let lnot_ (r1: reg) : reg  = C.lnot_ r1 
  let ult (r1: reg) (r2: reg) : node = C.ugt r2 r1 
  let slt (r1: reg) (r2: reg) : node = C.sgt r2 r1
  let ule (r1: reg) (r2: reg) : node = C.uge r2 r1
  let sle (r1: reg) (r2: reg) : node = C.sge r2 r1
  let uext (r1: reg) (size: int) : reg = C.uextend ~size r1 
  let sext (r1: reg) (size: int) : reg = C.sextend ~size r1 
  let trunc (r1: reg) (size: int) : reg = Array.sub r1 0 size  
  let concat (r1: reg) (r2: reg) : reg = Array.append r1 r2 
  let flatten (rs: reg list) : reg = Array.concat rs

  let reg_to_file ~(input_count: int) ?(inp_name_map: (int -> string) option) ~(name: string) (r: reg) : symbol =
    C.write_aiger_bin_temp ~input_count ?inp_name_map ~name r 

  module Deps = struct 
    type dep = (int, int Set.t) Map.t
    type deps = dep array
    type block_deps = (int * dep) array

    let dep_of_node = fun n -> CDeps.dep n
    let deps_of_reg = fun r -> CDeps.deps r
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

    let block_deps_of_reg (w: int) (r: reg) : block_deps = 
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
    
    (* FIXME: Some of these are unused as of now, but they seem useful 
       as part of the library, do we keep them? *)
    let dep_var_count (d: deps) : int = 
      Set.cardinal 
        (Array.fold_left (Set.union) Set.empty 
        (Array.map (fun dep -> Map.keys dep |> Set.of_enum) d)) 

    let merge_deps (d: deps) : dep =
      match Array.length d with
      | 0 -> Map.empty
      | _ -> Array.reduce (CDeps.merge_deps) d

    (* Assumes single_dep, returns range (bot, top) such that valid idxs are bot <= i < top *)
    let dep_ranges (d: deps) : (int, int * int) Map.t =
      let d = merge_deps d in
      Map.map (fun ds -> (Set.min_elt_opt ds |> Option.default (-1), 
                          Set.max_elt_opt ds |> Option.default (-1))) d

    (* Checks that all dependencies of r are in the set inps *)
    (* Each elements of inps is (id, width) *)
    let check_inputs (r: reg) (inps: (int * int) list) : bool = 
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

    let forall_inputs (check: int -> int -> bool) (r: reg) : bool =
      let d = deps_of_reg r in
      Array.for_all (fun d -> 
        Map.for_all (fun id bs -> Set.for_all (check id) bs) d) 
      d

    let rename_inputs (renamer: (int * int) -> (int * int) option) (r: reg) : reg =
      C.maps (fun (id, b) -> 
        Option.map (fun (id, b) -> input_node ~id b) (renamer (id, b)) 
      ) r 

    let excise_bit ?renamings (n: node) : node * (int, int * int) Map.t =
      CDeps.realign_inputs ?renamings n
  end
end

module type CircuitInterface = sig
  type flatcirc
  type ctype = 
    CArray of {width: int; count: int}
  | CBitstring of int 
  | CTuple of ctype list 
  | CBool
  type cinp = {
    type_ : ctype;
    id: int
  }
  type circ = { 
    reg: flatcirc ;
    type_: ctype ;
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 

  val pp_flatcirc : Format.formatter -> flatcirc -> unit
  
  module CArgs : sig
    type arg = 
    [ `Circuit of circuit
    | `Constant of zint   
    | `Init of int -> circuit 
    | `List of circuit list ]

    val arg_of_circuit : circuit -> arg
    val arg_of_zint : zint -> arg
    val arg_of_circuits : circuit list -> arg
    val arg_of_init : (int -> circuit) -> arg
    val pp_arg : Format.formatter -> arg -> unit
  end
  open CArgs

  module TranslationState : sig
    type state

    val empty_state : state

    val update_state_pv : state -> memory -> symbol -> circuit -> state
    val state_get_pv_opt : state -> memory -> symbol -> circuit option
    val state_get_pv : state -> memory -> symbol -> circuit 
    val state_get_all_memory : state -> memory -> (symbol * circuit) list
    val state_get_all_pv : state -> ((memory * symbol) * circuit) list

    val update_state : state -> ident ->  circuit -> state
    val state_get_opt : state -> ident -> circuit option
    val state_get : state -> ident -> circuit 
    val state_bindings : state -> (ident * circuit) list
    val state_lambdas : state -> cinp list
    val state_is_closed : state -> bool
    val state_close_circuit : state -> circuit -> circuit 
    val map_state_var : (ident -> circuit -> circuit) -> state -> state

    (* Circuit lambdas, for managing inputs *)
    val open_circ_lambda : state -> (ident * ctype) list -> state 
    val open_circ_lambda_pv  : state -> ((memory * symbol) * ctype) list -> state
    val close_circ_lambda : state -> state 
    val circ_lambda_oneshot : state -> (ident * ctype) list -> (state -> circuit) -> circuit

    val set_logger : state -> (string -> unit) -> state
    val log : state -> string -> unit
  end

  module BVOps : sig
    val bvget : circuit -> int -> circuit 
    val circuit_of_bvop : EcDecl.crb_bvoperator -> circuit  
    val circuit_of_parametric_bvop : EcDecl.crb_bvoperator -> arg list -> circuit
  end

  module ArrayOps : sig
      val array_get : circuit -> int -> circuit
      val array_set : circuit -> int -> circuit -> circuit 
      val array_oflist : circuit list -> circuit -> int -> circuit 
  end

  (* Circuit type utilities *)
  val size_of_ctype : ctype -> int
  val convert_type : ctype -> circuit -> circuit 
  val can_convert_input_type : ctype -> ctype -> bool

  (* Pretty Printers *)
  val pp_ctype : Format.formatter -> ctype -> unit
  val pp_cinp : Format.formatter -> cinp -> unit
  val pp_circ : Format.formatter -> circ -> unit
  val pp_circuit : Format.formatter -> circuit -> unit

  (* General utilities *)
  val circ_of_zint : size:int -> zint -> circ
  val circuit_of_zint : size:int -> zint -> circuit 

  
  (* Construct an input *)
  val new_input_circuit : ?name:[`Str of string | `Idn of ident | `Bad] -> ctype -> circ * cinp
  val input_of_ctype : ?name:[`Str of string | `Idn of ident | `Bad] -> ctype -> circuit

  (* Aggregation functions *)
  val circuit_aggregate : circuit list -> circuit
  val circuit_aggregate_inputs : circuit -> circuit

  (* Circuits representing booleans *)
  val circuit_true : circuit
  val circuit_false : circuit
  val circuit_and : circuit -> circuit -> circuit
  val circuit_or  : circuit -> circuit -> circuit
  val circuit_not : circuit -> circuit

  (* <=> circuit has not inputs (every input is unbound) *)
  val circuit_is_free : circuit -> bool
  
  (* Direct circuuit constructions *)
  val circuit_ite : c:circuit -> t:circuit -> f:circuit -> circuit
  val circuit_eq : circuit -> circuit -> circuit
  val circuit_eqs : circuit -> circuit -> circuit list


  (* Circuit tuples *)
  val circuit_tuple_proj : circuit -> int -> circuit 
  val circuit_tuple_of_circuits : circuit list -> circuit
  val circuits_of_circuit_tuple : circuit -> circuit list
 
  (* Avoid nodes for uninitialized inputs *)
  val circuit_uninit : ctype -> circuit
  val circuit_has_uninitialized : circuit -> int option

  (* Logical reasoning over circuits *)
  val circ_equiv : ?pcond:circuit -> circuit -> circuit -> bool
  val circ_sat   : circuit -> bool 
  val circ_taut  : circuit -> bool 

  (* Composition of circuit functions, should deal with inputs and call some backend *)
  val circuit_compose : circuit -> circuit list -> circuit

  (* Computing the function given by a circuit *)
  val compute : sign:bool -> circuit -> arg list -> zint option

  (* Mapreduce/Dependecy analysis related functions *)
  val circuit_slice : size:int -> circuit -> int -> circuit
  val circuit_slice_insert : circuit -> int -> circuit -> circuit 
  val fillet_circuit : circuit -> circuit list
  val fillet_tauts : ?logger:(string -> unit) -> circuit list -> circuit list -> bool
  val batch_checks : ?logger:(string -> unit) -> ?sort:bool -> ?mode:[`ByEq | `BySub ] -> circuit list -> circuit list

  (* Wraps the backend call to deal with args/inputs *) 
  val circuit_to_file : name:string -> circuit -> symbol

  val circuit_from_spec : ?name:symbol -> (ctype list * ctype) -> Lospecs.Ast.adef -> circuit
end

module MakeCircuitInterfaceFromCBackend(Backend: CBackend) : CircuitInterface = struct
  (* Module Types *)
  type flatcirc = Backend.reg
  type ctype = 
    CArray of {width: int; count: int; } 
  | CBitstring of int 
  | CTuple of ctype list 
  | CBool
  type circ = {
    reg: flatcirc; 
    type_: ctype; 
}
  type cinp = {
    type_ : ctype;
    id : int;
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 

  (* Exceptions *)
  type circconstructor = 
    | Slice of { slice_size: int; bitstring_size: int; offset: int }
    | ASlice of { slice_size: int; container_size: int; offset: int }
    | ASliceTy of ctype
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
  | CircComposeInvalidArguments (* FIXME: what is a useful error to print here ? *)
  | CircComposeBadNumberOfArguments of { expected: int; received: int}
  | CircEquivNonBoolPCond
  | CircSmtNonBoolCirc
  | CircComputeBadNumberOfArguments of { expected: int; received: int}
  | CircComputeInvalidArguments of int
  | UnsupportedTypeForFileOutput 
  | CloseWithoutLambda

  exception LowCircError of lowcircerror

  let lowcircerror (err: lowcircerror) =
    raise (LowCircError err)

 
  (* Helper functions *)
  let (|->) ((a,b)) ((f,g)) = (f a, g b)
  let idnt = fun x -> x

  let pp_flatcirc fmt fc = 
    let r = Backend.node_list_of_reg fc in
    List.iter (fun n ->
      Format.fprintf fmt "%a@." Backend.pp_node n
    ) r

  let circ_of_zint ~(size: int) (i: zint) : circ = 
    {reg = Backend.reg_of_zint ~size i; type_= CBitstring size }

  let circuit_of_zint ~(size: int) (i: zint) : circuit =
    ((circ_of_zint ~size i, []) :> circuit)

  let rec size_of_ctype (t: ctype) : int = 
    match t with 
    | CBitstring n -> n
    | CArray {width; count} -> width * count
    | CTuple tys -> List.sum (List.map size_of_ctype tys)
    | CBool -> 1

  (* Pretty printers *)
  let rec pp_ctype (fmt: Format.formatter) (t: ctype) : unit = 
    match t with
    | CArray {width; count}  -> Format.fprintf fmt "Array(%d@%d)" count width 
    | CBool -> Format.fprintf fmt "Bool"
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

  module TranslationState = struct
    type state = {
      circs    : circuit Mid.t;
      lambdas  : cinp list list; (* actually a stack *)
      pv_ids   : (ident * symbol, ident) Map.t; (* can be changed to int Msym.t if needed *)
      logger   : string -> unit;
    }

    let empty_state : state = {
      circs = Mid.empty;
      lambdas = [];
      pv_ids = Map.empty; (* can be changed to int Msym.t if needed *)
      logger = fun _ -> ();
    }

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
      { id = name.id_tag; type_ = t},
      ({ reg = Backend.input_of_size ~id:name.id_tag (size_of_ctype t); type_ = t}, [])
        
    (* Circuit lambdas, for managing inputs *)
    let open_circ_lambda (st: state) (bnds: (ident  * ctype) list) : state = 
      let inps, cs = List.map (fun (id, t) -> 
        st.logger @@ Format.asprintf "Opening circuit lambda for ident: (%s, %d)@." (name id) (tag id);
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

    (* FIXME: should we remove id from the mapping? *)
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

    let set_logger (st: state) (logger: string -> unit) : state = 
      { st with logger; } 

    let log (st: state) (s: string) : unit = 
      st.logger s
  end

  (* Inputs helper functions *)
  (* FIXME: maybe do something a bit more principled here ? After merge *)
  let merge_inputs (cs: cinp list) (ds: cinp list) : cinp list =
(*     if List.for_all2 (fun {id=id1; type_=ct1} {id=id2; type_=ct2} -> id1 = id2 && ct1 = ct2) cs ds then cs  *)
    if cs = ds then cs 
    else cs @ ds

  let merge_inputs_list (cs: cinp list list) : cinp list =
    List.fold_right (merge_inputs) cs []

  let merge_circuit_inputs (c: circuit) (d: circuit) : cinp list =
    merge_inputs (snd c) (snd d)

  let unify_inputs_renamer (target: cinp list) (inps: cinp list) : Backend.inp -> Backend.node option =
    let map = List.fold_left2 (fun map inp1 inp2 -> match inp1, inp2 with
      | {type_ = CBitstring w ; id=id_tgt},
        {type_ = CBitstring w'; id=id_orig} when w = w' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init w (fun i -> i))
      | {type_ = CArray {width=w; count=n}; id=id_tgt},
        {type_ = CArray {width=w'; count=n'}; id=id_orig} when w = w' && n = n' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w*n) (fun i -> i))
      | {type_ = CTuple tys ; id=id_tgt},
        {type_ = CTuple tys'; id=id_orig} when List.for_all2 (=) tys tys' -> 
          let w = List.sum (List.map size_of_ctype tys) in
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w) (fun i -> i))
      | {type_ = CBool; id=id_tgt},
        {type_ = CBool; id=id_orig} ->
          Map.add (id_orig, 0) (Backend.input_node ~id:id_tgt 0) map
      | _ -> lowcircerror (CircInputUnificationFailure (inp1, inp2))
    ) Map.empty target inps in
    fun inp -> Map.find_opt inp map

  (* Renames circuit2 inputs to match circuit 1 *)
  let unify_inputs (target: cinp list) ((c, inps): circuit) : circ = 
    let map_ = unify_inputs_renamer target inps in
    {c with reg = Backend.applys map_ c.reg}

  let inputs_contained (subi: cinp list) (supi: cinp list) : bool =
    List.compare_lengths subi supi < 0 &&
    List.for_all2 (=) (subi) (List.take (List.length subi) supi)
    
  let circuit_input_compatible ?(strict = false) ((c, _): circuit) (cinp: cinp) : bool =
    match c.type_, cinp with
    | CBitstring n, { type_ = CBitstring n' } when n = n' -> true
    | CArray {width=w; count=n}, { type_ = CArray {width=w'; count=n'}} when w = w' && n = n' -> true
    | CTuple (szs), { type_ = CTuple szs' } when List.all2 (=) szs szs' -> true
    | CBool, { type_ = CBool } -> true
    | CBool, { type_ = CBitstring 1 } when not strict -> true
    | CBitstring 1, { type_ = CBool } when not strict -> true
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
    {reg = (Backend.slice r idx (size_of_ctype ty)); type_ = ty}, inps

  let circuit_tuple_of_circuits (cs: circuit list) : circuit = 
    let tys = (List.map (fun (c : circuit) -> (fst c).type_) cs) in 
    let circ = Backend.flatten (List.map (fun (c : circuit) -> (fst c).reg) cs) in 
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
        ({reg = (Backend.slice tp idx sz); type_ = ty}, tpinps)))
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

  let convert_input_types ((c, inps) : circuit) (tys: ctype list) : circuit = 
    c, List.map2 (fun inp ty ->
      if can_convert_input_type inp.type_ ty then
        { inp with type_ = ty }
      else lowcircerror CircTyConversionFailure
    ) inps tys


  let input_of_ctype ?(name : [`Str of string | `Idn of ident | `Bad ] = `Str "input") (ct: ctype) : circuit = 
    let id, c = match name with
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_of_size ~id (size_of_ctype ct)    
    | `Idn idn -> let id = idn.id_tag in
      id, Backend.input_of_size ~id (size_of_ctype ct)    
    | `Bad ->
      -1, Backend.bad_reg (size_of_ctype ct)
    in
    { reg = c; type_ = ct; }, [{ id; type_ = ct; }]

  let new_input_circuit ?(name = `Str "input") (ty: ctype) : circ * cinp = 
    let c, inps = input_of_ctype ~name ty in
    c, List.hd inps

  let circuit_true  = {reg = Backend.reg_of_node Backend.true_; type_ = CBool}, [] 
  let circuit_false  = {reg = Backend.reg_of_node Backend.false_; type_ = CBool}, [] 

  let circuit_and ((c, cinps): circuit) ((d, dinps): circuit) =  
    if c.type_ = d.type_ then
      { reg = Backend.land_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      lowcircerror @@ CircConstructorInvalidArguments And

  let circuit_or ((c, cinps): circuit) ((d, dinps): circuit) = 
    if c.type_ = d.type_ then
      { reg = Backend.lor_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      lowcircerror @@ CircConstructorInvalidArguments Or

  let circuit_not ((c, cinps): circuit) =
    {c with reg = Backend.lnot_ c.reg}, cinps

  let circuit_is_free (f: circuit) : bool = List.is_empty @@ snd f 

  let circuit_ite ~(c: circuit) ~(t: circuit) ~(f: circuit) : circuit =
    let strict = true in (* FIXME: Decide which behaviour we want, post PR *)
    let inps = match c, t, f with
    | (_, []), (_, []), (_, []) when strict -> []
    | (_, cinps), (_, tinps), (_, finps) when (not strict) && cinps = tinps && cinps = finps -> cinps
    | _ -> assert false
    in
    let c = match (fst c).type_ with
    | CBool -> Backend.node_of_reg (fst c).reg
    | _ -> assert false
    in
    let res_r = Backend.reg_ite c (fst t).reg (fst f).reg in
    match ((fst t).type_, (fst f).type_) with
    | CBitstring nt, CBitstring nf when nt = nf -> {reg = res_r; type_ = (fst t).type_}, inps
    | CArray {width=wt; count=nt}, CArray {width=wf; count=nf} when wt = wf && nt = nf -> {reg = res_r; type_ = (fst t).type_}, inps  
    | CTuple szs_t, CTuple szs_f when List.all2 (=) szs_t szs_f -> {reg = res_r; type_ = (fst t).type_}, inps 
    | CBool, CBool -> {reg = res_r; type_ = (fst t).type_}, inps
    | _ -> lowcircerror @@ CircConstructorInvalidArguments Ite

  (* TODO: type check? *)
  let circuit_eq (c: circuit) (d: circuit) : circuit =  
    match (fst c).type_, (fst d).type_ with
    | (CArray _), (CArray _) 
    | (CTuple _), (CTuple _) 
    | (CBitstring _), (CBitstring _) ->
      {reg = (Backend.reg_eq (fst c).reg (fst d).reg |> Backend.reg_of_node); type_ = CBool}, merge_inputs (snd c) (snd d)
    | CBool, CBool ->
      {reg = (Backend.reg_eq (fst c).reg (fst d).reg |> Backend.reg_of_node); type_ = CBool}, merge_inputs (snd c) (snd d)
    | CBool, CBitstring 1 ->
      {reg = (Backend.reg_eq (fst c).reg (fst d).reg |> Backend.reg_of_node); type_ = CBool}, merge_inputs (snd c) (snd d)
    | CBitstring 1, CBool ->
      {reg = (Backend.reg_eq (fst c).reg (fst d).reg |> Backend.reg_of_node); type_ = CBool}, merge_inputs (snd c) (snd d)
    | _ -> lowcircerror @@ CircConstructorInvalidArguments Eq

  (* Ignore types, do extensionally over bits, return the circuits evaluating to the condition *)
  let circuit_eqs ((c, cinps): circuit) ((d, dinps): circuit) : circuit list = 
    let inps = merge_inputs cinps dinps in

    if (size_of_ctype c.type_ <> size_of_ctype d.type_) then 
      lowcircerror @@ CircConstructorInvalidArguments Eqs;

    let cs = Backend.node_list_of_reg c.reg in
    let ds = Backend.node_list_of_reg d.reg in
    List.map2 (fun c d ->
      let r = Backend.node_eq c d |> Backend.reg_of_node in
      {reg = r; type_ = CBool}, inps) cs ds

    
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
            Some (Backend.get c.reg idx)
          with Invalid_argument _ -> None 
          end
        | CBool when idx = 0 -> Some (Backend.node_of_reg c.reg)
        | _ -> None
      ) 
    in
    
    let circ = {(fst c) with reg = Backend.applys map_ (fst c).reg} in
    let inps = merge_inputs_list (List.snd args) in
    (circ, inps)

  (* Functions for dealing with uninitialized inputs *)
  let circuit_uninit (t: ctype) : circuit = 
    let c, _ = input_of_ctype ~name:`Bad t in
    c, []
    
  let circuit_has_uninitialized (c: circuit) : int option =
    Backend.have_bad (fst c).reg

  let circ_equiv ?(pcond:circuit option) ((c1, inps1): circuit) ((c2, inps2): circuit) : bool = 
    let pcond = Option.map (convert_type CBool) pcond in (* Try to convert to bool *) 
    let pcc = match pcond with
    | Some ({reg = b; type_ = CBool}, pcinps) -> 
        Backend.apply (unify_inputs_renamer inps1 pcinps) (Backend.node_of_reg b)
    | None -> Backend.true_ 
    | _ -> lowcircerror CircEquivNonBoolPCond 
    in
    (* This throws, but we let it propagate upwards *)
    let c2 = unify_inputs inps1 (c2, inps2) in
    let inps = List.map (function 
      | { type_ = CBool; id } -> (id, 1)
      | { type_ = CBitstring w; id } -> (id, w) 
      | { type_ = CArray {width=w1; count=w2}; id } -> (id, w1*w2)
      | { type_ = CTuple tys; id } -> (id, List.sum @@ List.map size_of_ctype tys) 

    ) inps1 in
    if (c1.type_ = c2.type_) then
      Backend.equiv ~inps ~pcond:pcc c1.reg c2.reg
    else false
    
  let circ_sat ((c, inps): circuit) : bool =
    let c = match c with 
    | {type_ = CBool; reg} -> Backend.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
    in
    let inps = List.map (function 
      | { type_ = CBool; id } -> (id, 1)
      | { type_ = CBitstring w; id } -> (id, w) 
      | { type_ = CArray {width=w1; count=w2}; id } -> (id, w1*w2)
      | { type_ = CTuple tys; id } -> (id, List.sum @@ List.map size_of_ctype tys) 

    ) inps in
    Backend.sat ~inps c 
    
  let circ_taut ((c, inps): circuit) : bool = 
    let c = match c with 
    | {type_ = CBool; reg} -> Backend.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
    in
    let inps = List.map (function 
      | { type_ = CBool; id } -> (id, 1)
      | { type_ = CBitstring w; id } -> (id, w) 
      | { type_ = CArray {width=w1; count=w2}; id } -> (id, w1*w2)
      | { type_ = CTuple tys; id } -> (id, List.sum @@ List.map size_of_ctype tys) 

    ) inps in
    Backend.taut ~inps c 

  (* Inputs mean different things depending on circuit type *)
  (* Allow unaligned slices *)
  let circuit_slice ~(size:int) ((c, inps): circuit) (offset: int) : circuit =
    try 
      {reg = Backend.slice c.reg offset size; type_ = CBitstring size}, inps
    with Backend.BadSlice `Get ->
      lowcircerror @@ CircConstructorInvalidArguments (Slice {
        slice_size = size;
        bitstring_size = Backend.size_of_reg c.reg;
        offset;
      })
    
  (* Slice by container index *)
  let circuit_aslice ~(size:int) ((c, inps): circuit) (offset: int) : circuit =
    match c.type_ with 
    | CArray {width=w; count=n} -> 
      if (n < size + offset) || size < 0 || offset < 0 then
        lowcircerror @@ CircConstructorInvalidArguments (ASlice {
          slice_size = size;
          container_size = n;
          offset;
        });

      {reg = Backend.slice c.reg offset size; type_ = CArray {width=w; count=size}}, inps

    | CBitstring w -> lowcircerror @@ CircConstructorInvalidArguments (ASliceTy (CBitstring w))
    | CTuple tys ->
        if List.compare_length_with tys (offset + size) < 0 
        || offset < 0 || size < 0 then
          lowcircerror @@ CircConstructorInvalidArguments (ASlice {
            slice_size = size;
            container_size = List.length tys;
            offset;
          });

        let offset, tys = List.takedrop offset tys in
        let offset = List.sum @@ List.map size_of_ctype offset in
        let tys = (List.take size tys) in 
        let sz = List.sum @@ List.map size_of_ctype tys in
        {reg = (Backend.slice c.reg offset sz); type_ = CTuple tys}, inps

    | CBool -> 
        lowcircerror @@ CircConstructorInvalidArguments (ASliceTy CBool)


  (* Does not type check *)
  let circuit_slice_insert ((orig_c, orig_inps): circuit) (idx: int) ((new_c, new_inps): circuit) : circuit = 
    try 
      { orig_c with reg = (Backend.insert orig_c.reg idx new_c.reg)}, merge_inputs orig_inps new_inps
    with Backend.BadSlice `Set ->
      lowcircerror @@ CircConstructorInvalidArguments (SliceSet {
        slice_size = Backend.size_of_reg new_c.reg;
        bitstring_size = Backend.size_of_reg orig_c.reg;
        offset = idx;
      })

  (* 
     Takes a circuit and uses dependency analysis to separate it into 
     subcircuits corresponding to the output bits
     
     In particular, equivalence between two circuits is equivalent 
     to equivalence between the subcircuits 

     Implicitly flattens everything to bitstrings

     TODO: add functionality for user specified lane size
  *)
  let fillet_circuit ((c, inps) : circuit) : circuit list = 
    let r = c.reg |> Backend.node_list_of_reg in
    List.map (fun n ->
      let new_inps = List.map (fun {id=_;type_} ->
        {id=EcIdent.create "_" |> tag; type_}) inps 
      in
      let renamings = List.combine 
        (List.map (fun {id} -> id) inps)
        (List.map (fun {id} -> id) new_inps)
      |> List.to_seq |> Map.of_seq 
      in
      let renamings = fun v -> Map.find_opt v renamings in
      let n', shifts = Backend.Deps.excise_bit ~renamings n in

      let new_inps = List.filter_map (fun {id;_} ->
        match Map.find_opt id shifts with
        | Some (low, hi) -> Some {id; type_ = CBitstring (hi - low + 1)}
        | None -> None
      ) new_inps in
      { reg = Backend.reg_of_node n';
        type_ = CBool },
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
    ?(logger : (string -> unit) option) 
    ?(sort = true) 
    ?(mode : [`ByEq | `BySub] = `ByEq) 
     (checks: circuit list) 
    : circuit list 
  =
    (* Order by dependencies *)
    let checks = if sort then begin 

    let checks = List.map (fun (c, inps) ->
      (c, inps), Backend.(Deps.dep_of_node (node_of_reg c.reg))) checks in
    let checks = List.stable_sort (fun (_, d1) (_, d2) ->
      let m1 = (Map.keys d1 |> Set.of_enum |> Set.min_elt_opt) in 
      let m2 = (Map.keys d2 |> Set.of_enum |> Set.min_elt_opt) in 
      (* FIXME: Check this *)
      match m1, m2 with
      | None, None -> 0
      | None, Some _ -> -1
      | Some _, None -> 1
      | Some m1, Some m2 ->
      let c1 = Int.compare m1 m2 in
      if c1 = 0 then (* FIXME: check default value V V *)
        Int.compare (Map.find m1 d1 |> Set.min_elt_opt |> Option.default (-1)) (Map.find m1 d2 |> Set.min_elt_opt |> Option.default (-1))
      else
        c1
    ) checks in
    checks 
    end else
      List.map (fun c ->
        c, Backend.(Deps.dep_of_node (node_of_reg (fst c).reg))) checks
    in

    let rec doit (acc: circuit list) (cur, d: circuit * Backend.Deps.dep) (cs: (circuit * Backend.Deps.dep) list) : circuit list =
      match cs with 
      | [] -> (cur::acc)
      | (c, d')::cs -> 
(*
        FIXME: do we keep this? also add log levels *)
        Option.may (fun f -> f @@ 
          Format.asprintf "Comparing deps:@.%a@.To deps:@.%a@."
          Backend.Deps.pp_dep d 
          Backend.Deps.pp_dep d') 
        logger;
        begin match mode with
          | `ByEq when Backend.Deps.deps_equal d d' -> 
            doit acc ((circuit_and cur c), d) cs
          | `BySub when Backend.Deps.(dep_contained d d') -> 
            doit acc ((circuit_and cur c), d') cs
          | `BySub when Backend.Deps.(dep_contained d' d) ->
            doit acc ((circuit_and cur c), d) cs
          | _ ->
            Option.may (fun f -> f @@ Format.asprintf "Consolidated lane deps: %a@." Backend.Deps.pp_dep d) logger;
            doit (cur::acc) (c, d') cs
        end
    in

    match checks with
    | [] -> []
    | c::cs -> doit [] c cs

   
  let attach_compatible_pres ?(mode: [`Cont | `Eq | `Int] = `Cont) (pres: (circuit * Backend.Deps.dep) list) ((post_circ, _) as post: circuit) : circuit =
    let d = Backend.(Deps.dep_of_node (node_of_reg post_circ.reg)) in
    let compat_pres = List.filteri (fun _i (_c, pre_dep) ->
      match mode with
      | `Cont -> Backend.Deps.dep_contained pre_dep d
      | `Eq -> Backend.Deps.deps_equal pre_dep d
      | `Int -> Backend.Deps.deps_intersect pre_dep d
    ) pres in
    let compat_pres = List.fst compat_pres in
    let pre = List.fold_left circuit_and circuit_true compat_pres in
    circuit_or (circuit_not pre) post

    let sublimate_inputs ((c, cinps): circuit) : circuit = 
    assert (c.type_ = CBool);
    let node_c = Backend.node_of_reg c.reg in
    let node_c, shifts = Backend.Deps.excise_bit node_c in
    (* FIXME: do this in a more principled way (the types) after merge *)
    let inps = List.filter_map (fun {id; _} ->
      match Map.find_opt id shifts with
      | Some (low, hi) -> Some {id; type_ = CBitstring (hi - low + 1)}
      | None -> None 
    ) cinps in 
    let c = Backend.reg_of_node node_c in
    { reg = c; type_ = CBool}, inps


  (* FIXME: Review later? *)
  let collapse_lanes ?(logger : (string -> unit) option) (lanes: circuit list) =
    (* Circuit structural equality after renaming *)
    let (===) (c1: circ) (c2: circ) : bool = 
      let n', _ = Backend.node_of_reg c1.reg |> Backend.Deps.excise_bit in
      let n, _ = Backend.node_of_reg c2.reg |> Backend.Deps.excise_bit in
      Backend.nodes_eq n n'
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
    (* FIXME: optimize later *)
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
            (Option.may (fun f -> f "Cannot correctly infer lanes, defaulting to bruteforce checking@.") logger;
            (c::cs))
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
  let fillet_tauts ?(logger: (string -> unit) option) (pres: circuit list) (posts: circuit list) : bool =
    (* Assumes everything is single bit outputs. FIXME: does it? *)
    let posts = List.filter_map (fun ((postc, _) as post) -> 
      if Backend.nodes_eq (Backend.node_of_reg postc.reg) Backend.true_ then None
      else Some post
    ) posts in
  
    match posts with
    | [] -> true
    | posts ->
      if (not (List.for_all (fun ({type_;reg=_}, _) -> type_ = CBool) pres))
      || (not (List.for_all (fun ({type_;reg=_}, _) -> type_ = CBool) posts)) then
        lowcircerror CircSmtNonBoolCirc;
      let pres = List.map (fun ((c, _) as circ) -> circ,
        Backend.Deps.dep_of_node (Backend.node_of_reg c.reg)) pres in
      let posts = List.map (attach_compatible_pres ~mode:`Int pres) posts in
      let posts = collapse_lanes ?logger posts in

      Option.may (fun f -> f @@ Format.asprintf "%d conditions to check after structural equality collapse@." (List.length posts)) logger;

      List.mapi (fun i post -> 
        Option.may (fun f -> f @@ Format.asprintf "Checking equivalence for bit %d@." i) logger;

(*         let res = fillet_taut pres post in  *)
        let post = sublimate_inputs post in
        let res = circ_taut post in
        if not res then 
          Option.may (fun f -> f @@ Format.asprintf "Failed for bit %d@." i) logger;
        res) posts |>
      List.for_all identity
   
  let compute ~(sign: bool) ((r, inps) as c: circuit) (args: arg list) : zint option = 
    begin match r.type_ with
    | CBitstring _ -> ()
    | _ -> assert false (* TODO: FIXME Add functionality for other or add exception *)
    end;

    if List.compare_lengths args inps <> 0 
    then lowcircerror @@ CircComputeBadNumberOfArguments 
      { expected = List.length inps;
        received = List.length args; };

    let args = List.map2i (fun i arg inp ->
    match arg, inp with
    | `Circuit c, inp when circuit_input_compatible c inp -> c
    | `Constant i, {type_ = CBitstring size} -> { reg = (Backend.reg_of_zint ~size i); type_ = CBitstring size}, []
    | _ -> lowcircerror @@ CircComputeInvalidArguments i
    ) args inps 
    in
    match circuit_compose c args with
    | {reg = r; type_ = CBitstring _}, [] -> 
      begin try 
        Some (if sign 
        then Backend.szint_of_reg r
        else Backend.uzint_of_reg r)
      with Backend.NonConstantCircuit -> None
      end
    | _, _::_ -> assert false (* Should not happen *)
    | _ -> assert false (* Should not happen *)

  let circuit_aggregate (cs: circuit list) : circuit =
    let inps = List.snd cs in
    let cs = List.map (fun c -> (fst c).reg) cs in
    let c = Backend.flatten cs in
    let inps = merge_inputs_list inps in
    {reg = c; type_ = CBitstring (Backend.size_of_reg c)}, inps

  let input_aggregate_renamer (inps: cinp list) : cinp * (Backend.inp -> Backend.node option) =
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
      | { type_ = CBool; id} ->
        (size + 1, Map.add id (size, 1) map)
      ) (0, Map.empty) inps
    in
    {type_ = CBitstring size; id=new_id},
    fun (id, bit) -> 
      let base_sz = Map.find_opt id map in
      Option.bind base_sz (fun (base, sz) ->
        let idx = bit + base in
        if bit >= 0 && bit < sz then 
        Some (Backend.input_node ~id:new_id idx)
        else None
      ) 

  let circuit_aggregate_inputs ((c, inps): circuit) : circuit =
    let inp, renamer = input_aggregate_renamer inps in
    {c with reg = Backend.applys renamer c.reg}, [inp]

  (* FIXME: do implicit conversion to this type before writing or enforce explicit conversion ? *)
  let circuit_to_file ~(name: string) ((c, inps): circuit) : symbol =
    match c, inps with
    | {reg = r; type_ = CBitstring _}, {type_ = CBitstring w; id}::[] -> (* TODO: rename inputs? *)
      Backend.reg_to_file ~input_count:w ~name (Backend.applys (fun (id_, i) -> if id_ = id then Some (Backend.input_node ~id:0 (i+1)) else None) r)
    | _ -> lowcircerror @@ UnsupportedTypeForFileOutput

  let circuit_from_spec ?(name: symbol option) ((arg_tys, ret_ty) : (ctype list * ctype)) (spec: Lospecs.Ast.adef) : circuit = 
    let c = Backend.circuit_from_spec spec in

    let name = match name with 
    | Some name -> name ^ "_spec_input"
    | None -> "spec_input"
    in

    let cinps, inps = List.mapi (fun i ty -> 
      let id = EcIdent.create (name ^ "_" ^ (string_of_int i)) |> tag in
      let size : int = size_of_ctype ty in
      (Backend.input_of_size ~id size, { type_ = ty; id = id; } )
      ) arg_tys |> List.split in
    let c = c cinps in
    { reg = c; type_ = ret_ty}, inps (* TODO: type checking ? *)
(*     { reg = c; CBitstring c, inps) |> convert_type ret_ty *)

    module BVOps = struct
      let bvget (c: circuit) (i: int) : circuit = 
        match c with 
        | {reg; type_ = CBitstring n}, inps when 0 <= i && i < n -> 
          begin try
            {reg = Backend.reg_of_node (Backend.get reg i); type_ = CBool}, inps
          with Backend.GetOutOfRange ->
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

      (* FIXME: what do we want for out of bounds extract? Decide later *)
      | { kind = `Extract ((_, Some _), (_, Some w_out)) } -> 
        begin match args with
        | [ `Circuit (({type_ = CBitstring _}, _ ) as c) ; `Constant i ] ->
          circuit_slice ~size:w_out c (to_int i) 
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
          (List.init n (fun i -> {reg = (Backend.slice arr (i*w_i) w_i); type_ = CBitstring w_i}, []))
          in
          (* Inputs of all components should match after map *)
          if not (List.for_all ((=) (List.hd inps)) inps) then 
            (* FIXME: Careful with input modelling, if abstraction breaks this breaks
               post PR work *)
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let inps = List.hd inps in
          let circ = { reg = (Backend.flatten circs); type_ = CArray {width=w_o; count=n}} in  
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
              | {type_ = CBitstring _; reg = r} when Backend.size_of_reg r = w_o -> r 
            (* Invalid type for init component *)
            | _ -> assert false) (* Should be caught by EC typechecking + binding correctness *) 
          circs in
          (* Inputs should be uniform across components after mapping *)
          if not (List.for_all ((=) (List.hd cinps)) cinps) then
            (* FIXME: Careful with input modelling, if abstraction breaks this breaks
               post PR work *)
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let cinps = List.hd cinps in
          {type_ = CArray {width=w_o; count=n} ; reg = Backend.flatten circs}, cinps 
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | { kind = `Init (_, Some w) } -> 
        begin match args with 
        | [ `Init init_f ] ->
          let circs, cinps = List.split @@ List.init w init_f in
          let circs = List.map 
            (function 
            (* FIXME: bad abstraction, fix after PR *)
            | {type_ = CBitstring 1; reg = b}
            | {type_ = CBool; reg = b} -> Backend.node_of_reg b 
            (* Return type should be bool (= bit) for components *)
            | _ -> assert false) (* Should be caught by EC typechecking + binding correctness *)
            circs
          in
          if not (List.for_all ((=) (List.hd cinps)) cinps) then
            (* FIXME: Careful with input modelling, if abstraction breaks this breaks
               post PR work *)
            assert false; (* Should be caught by EC typechecking + binding correctness *)
          let cinps = List.hd cinps in
          {type_ = CBitstring w; reg = (Backend.reg_of_node_list circs)}, cinps
        | _ -> assert false (* Should be caught by EC typechecking + binding correctness *)
        end
      | _ -> assert false (* Should not happen because calls should be guarded by call to op_is_parametric_bvop *)


      let circuit_of_bvop (op: EcDecl.crb_bvoperator) : circuit = 
      match op with
      | { kind = `Add (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.add c1 c2 )}, [inp1; inp2] 

      | { kind = `Sub (_, Some size) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.sub c1 c2)}, [inp1; inp2] 

      | { kind = `Mul  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.mul c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.udiv c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.sdiv c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.umod c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.smod c1 c2)}, [inp1; inp2] 
        (* Should this be mod or rem? TODO FIXME*)

      | { kind = `Shl  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.lshl c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.lshr c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.ashr c1 c2)}, [inp1; inp2] 

      | { kind = `Shls  ((_, Some size1), (_, Some size2)) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (Backend.lshl c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), false) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (Backend.lshr c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), true) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size2) in
        {type_ = CBitstring size1; reg = (Backend.ashr c1 c2)}, [inp1; inp2] 

      | { kind = `Rol  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.rol c1 c2)}, [inp1; inp2] 

      | { kind = `Ror  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.ror c1 c2)}, [inp1; inp2] 

      | { kind = `And  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.land_ c1 c2)}, [inp1; inp2] 

      | { kind = `Or   (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.lor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Xor  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring size; reg = (Backend.lxor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Not  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring size; reg = (Backend.lnot_ c1)}, [inp1] 

      | { kind = `Opp  (_, Some size) } -> 
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring size; reg = (Backend.opp c1)}, [inp1] 

      | { kind = `Lt ((_, Some size), false) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.ult c1 c2)}, [inp1; inp2] 
      
      | { kind = `Lt ((_, Some size), true) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.slt c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), false) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.ule c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), true) } ->
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring size) in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.sle c1 c2)}, [inp1; inp2] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), false) } ->
        (* assert (size <= out_size); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring out_size; reg = (Backend.uext c1 out_size)}, [inp1] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), true) } ->
        (* assert (size <= out_size); *)  
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in 
        {type_ = CBitstring out_size; reg = (Backend.sext c1 out_size)}, [inp1] 

      | { kind = `Truncate ((_, Some size), (_, Some out_sz)) } ->
        (* assert (size >= out_sz); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring size) in
        {type_ = CBitstring out_sz; reg = (Backend.trunc c1 out_sz)}, [inp1] 

      | { kind = `Concat ((_, Some sz1), (_, Some sz2), (_, Some szo)) } ->
        (* assert (sz1 + sz2 = szo); *)
        let {reg = c1;_}, inp1 = new_input_circuit (CBitstring sz1) in 
        let {reg = c2;_}, inp2 = new_input_circuit (CBitstring sz2) in
        {type_ = CBitstring szo; reg = (Backend.concat c1 c2)}, [inp1; inp2] 

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

    module ArrayOps = struct
      let array_get (c: circuit) (i: int) : circuit = 
        match c with 
        | ({reg = c; type_ = CArray {width=w; count=n}}, inps) -> 
          begin try
            { type_ = CBitstring w; reg = (Backend.slice c (i*w) w)}, inps  
          with Backend.BadSlice `Get ->
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
            { type_ = CArray {width=w; count=n}; reg = (Backend.insert arr (pos * w) bs)},
            merge_inputs inps cinps
          with Backend.BadSlice `Set -> 
            lowcircerror @@ CircConstructorInvalidArguments (ASet {
              container_size = n;
              index = pos;
            })
          end
        | _ -> assert false (* Programming error *)

    (* FIXME: review this functiono | FIXME: Not axiomatized in QFABV.ec file *)
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
        { type_ = CArray {width=Backend.size_of_reg (List.hd circs); count=len}; reg = (Backend.flatten circs)}, merge_inputs_list inps 
    end
end

include MakeCircuitInterfaceFromCBackend(LospecsBack)
include CArgs
include TranslationState
include BVOps
include ArrayOps

let reset_backend_state () = 
  C.HCons.clear ();
  CDeps.reset_state ()
