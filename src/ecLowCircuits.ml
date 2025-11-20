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

module HL = struct
  include Lospecs.Hlaig
end

module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

exception CircError of string

let debug : bool = true

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

    (* Assumes only one reg -> reg and parallel blocks *)
    val is_splittable : int -> int -> deps -> bool

    val are_independent : block_deps -> bool

    val single_dep : deps -> bool
    (* Assumes single_dep *)
    val dep_range : deps -> int * int
    (* Checks if first dep is a subset of second dep *) 
    val dep_contained : dep -> dep -> bool
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
    Format.fprintf fmt "%a" Lospecs.Aig.pp_node n

  exception NonConstantCircuit (* FIXME: Rename later *)

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
  (* FIXME: throws array error, error handling TODO *)
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
    let open HL in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_equiv ?inps r1 r2 pcond  

  let sat ?(inps: inp list option) (n: node) : bool =
    let open HL in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_sat ?inps n 

  let taut ?(inps: inp list option) (n: node) : bool =
    let open HL in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_taut ?inps n 

  let slice (r: reg) (idx: int) (len: int) : reg = 
    Array.sub r idx len

  let subcirc (r: reg) (outs: int list) : reg =
    List.map (fun i -> r.(i)) outs |> Array.of_list

  let insert (r: reg) (idx: int) (r_in: reg) : reg =
    let ret = Array.copy r in
    Array.blit r_in 0 ret idx (Array.length r_in);
    ret

  (* FIXME: Error handling *)
  let get (r: reg) (idx: int) = r.(idx)

  let permute (w: int) (perm: int -> int) (r: reg) : reg =
    if debug then Format.eprintf "Applying permutation to reg of size %d with block size of %d@." (size_of_reg r) w;
    Array.init (size_of_reg r) (fun i ->
      let block_idx, bit_idx = perm (i / w), (i mod w) in
      if block_idx < 0 then None 
      else
      let idx = block_idx*w + bit_idx in
      Some r.(idx)
    ) |> Array.filter_map (fun x -> x)


  (* Node operations *)
  let band : node -> node -> node = C.and_
  let bor : node -> node -> node = C.or_
  let bxor : node -> node -> node = C.xor
  let bnot : node -> node = C.neg
  let bxnor : node -> node -> node = C.xnor
  let bnand : node -> node -> node = C.nand
  let bnor : node -> node -> node = fun n1 n2 -> C.neg @@ C.or_ n1 n2 

  (* FIXME: maybe convert to BigInt? *)
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

    let dep_of_node = fun n -> HL.dep n
    let deps_of_reg = fun r -> HL.deps r
    let block_deps_of_deps (w: int) (d: deps) : block_deps = 
      assert (Array.length d mod w = 0);
      Array.init (Array.length d / w) (fun i ->
        let deps = Array.sub d (i*w) w in
        let block = Array.fold_left (fun acc m ->
          Map.merge (fun idx d1 d2 ->
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

    (* Assumes only one reg -> reg and parallel blocks *)
    let is_splittable (w_in: int) (w_out: int) (d: deps) : bool =
      match Set.cardinal 
        (Array.fold_left (Set.union) Set.empty 
        (Array.map (fun dep -> Map.keys dep |> Set.of_enum) d)) 
      with 
      | 0 -> true
      | 1 ->
        let blocks = block_deps_of_deps w_out d in
        if debug then Format.eprintf "Checking block width...@.";
        Array.fold_left_map (fun idx (width, d) ->
          if Map.is_empty d then idx + width, true
          else
          let _, bits = Map.any d in
          idx + width, Set.is_empty bits ||
          let base = Set.at_rank_exn 0 bits in
          if Set.for_all (fun bit ->
            let dist = bit - base in
            if 0 <= dist && dist < w_in then true else false
(*
            (Format.eprintf "Current bit: %d | Current dist: %d | Limit: %d@." bit dist w_in; 
            Format.eprintf "Base for current block: %d@." base;
            false)
*)
          ) bits then true else
          begin
            if debug then Format.eprintf "Bad block: [%d..%d] %a@." idx (idx + width - 1) pp_dep d; false
          end
        ) 0 blocks |> snd |> Array.for_all (fun x -> x)
      | _ -> begin
        if debug then Format.eprintf "Failed first check@\n"; 
        if debug then Format.eprintf "Map keys: ";
        if debug then Array.iteri (fun i dep ->
          Format.eprintf "Bit %d: " i;
          List.iter (Format.eprintf "%d") (Map.keys dep |> List.of_enum);
          Format.eprintf "@\n") d;
        false
      end
        

    let are_independent (bd: block_deps) : bool =
      let exception BreakOut in
      try 
        ignore @@ Array.fold_left (fun acc (_, d) ->
          Map.merge (fun _ d1 d2 ->
            match d1, d2 with
            | None, None -> None
            | Some d, None | None, Some d -> Some d
            | Some d1, Some d2 ->
              if not (Set.disjoint d1 d2) then raise BreakOut else
              Some (Set.union d1 d2)
          ) acc d
        ) Map.empty bd;
        true
      with BreakOut ->
        false


    let single_dep (d: deps) : bool =
      match Set.cardinal 
        (Array.fold_left (Set.union) Set.empty 
        (Array.map (fun dep -> Map.keys dep |> Set.of_enum) d)) 
      with 
      | 0 | 1 -> true
      | _ -> false

    (* Assumes single_dep, returns range (bot, top) such that valid idxs are bot <= i < top *)
    let dep_range (d: deps) : int * int =
      assert (single_dep d);
      let idxs = 
        Array.fold_left (fun acc d -> 
        Set.union (Map.fold Set.union d Set.empty) acc) Set.empty d
      in
      if debug then Format.eprintf "%a@." pp_deps d;
      if debug then Format.eprintf "Dep range for dependencies:@.";
      if debug then Set.iter (fun i -> Format.eprintf "%d " i) idxs;
      if debug then Format.eprintf "@.Min: %d | Max: %d@." (Set.min_elt idxs) (Set.max_elt idxs);
      (Set.min_elt idxs, Set.max_elt idxs + 1)

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

    let dep_contained (subd: dep) (superd: dep) : bool =
      Map.for_all (fun id bits ->
        match Map.find_opt id superd with
        | None -> false
        | Some superbits -> Set.subset bits superbits
      ) subd

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
      HL.realign_inputs ?renamings n
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
(*     val map_state_pv : (symbol -> circuit -> circuit) -> state -> state *)

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
    val circ_lambda_oneshot : state -> (ident * ctype) list -> (state -> 'a * circuit) -> 'a * circuit (* FIXME: rename or redo *)
  end

  module BVOps : sig
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

  (* Type conversions *)
  (* TODO: Redo this *)
(*
  val cbool_of_circuit : ?strict:bool -> circuit -> circuit
  val cbitstring_of_circuit : ?strict:bool -> circuit -> circuit
  val carray_of_circuit : ?strict:bool -> circuit -> circuit
  val ctuple_of_circuit : ?strict:bool -> circuit -> circuit
*)

  (* Type constructors *)
  val new_cbool_inp : ?name:[`Str of string | `Idn of ident] -> unit -> circ * cinp
  val new_cbitstring_inp : ?name:[`Str of string | `Idn of ident] -> int -> circ * cinp
  val new_carray_inp : ?name:[`Str of string | `Idn of ident] -> int -> int -> circ * cinp
  val new_ctuple_inp : ?name:[`Str of string | `Idn of ident] -> ctype list -> circ * cinp

  (* Construct an input *)
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
  val is_decomposable : int -> int -> circuit -> bool
  val decompose : int -> int -> circuit -> circuit list
  val permute : int -> (int -> int) -> circuit -> circuit
  val align_inputs : circuit -> (int * int) option list -> circuit
  val circuit_slice : size:int -> circuit -> int -> circuit
  val circuit_slice_insert : circuit -> int -> circuit -> circuit 
  val fillet_circuit : circuit -> circuit list
  val fillet_tauts : circuit list -> circuit list -> bool
  val batch_checks : ?sort:bool -> circuit list -> circuit list

  (* Wraps the backend call to deal with args/inputs *) 
  val circuit_to_file : name:string -> circuit -> symbol

  val circuit_from_spec : ?name:symbol -> (ctype list * ctype) -> Lospecs.Ast.adef -> circuit
end

module MakeCircuitInterfaceFromCBackend(Backend: CBackend) : CircuitInterface = struct
  (* Module Types *)
  type flatcirc = Backend.reg
  type width = int
  type count = int
  type ctype = 
    CArray of {width: int; count: int; } 
  | CBitstring of width 
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
    }

    let empty_state : state = {
      circs = Mid.empty;
      lambdas = [];
      pv_ids = Map.empty; (* can be changed to int Msym.t if needed *)
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

    let state_get_pv : state -> memory -> symbol -> circuit = (fun st m s -> Option.get @@ state_get_pv_opt st m s) (* FIXME *)
    let state_get_all_pv (st: state) : ((memory * symbol) * circuit) list = 
      let pvs = Map.bindings st.pv_ids in
      List.filter_map (fun (pv, id) -> match Mid.find_opt id st.circs with | None -> None | Some c -> Some (pv, c)) pvs 

    let state_get_all_memory (st: state) (m: memory) : (symbol * circuit) list = 
      List.filter_map (fun ((m_, s), c) -> if m = m_ then Some (s, c) else None) 
        (state_get_all_pv st)

(*     let map_state_pv : (symbol -> circuit -> circuit) -> state -> state = assert false *)

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
        if debug then Format.eprintf "Opening circuit lambda for ident: (%s, %d)@." (name id) (tag id);
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
      | [] -> raise (CircError "no lambda to close in state")
      | inps::lambdas ->
        {st with lambdas = lambdas;
           circs = Mid.map (fun (c, cinps) -> (c, inps @ cinps)) st.circs }

    let circ_lambda_oneshot (st: state) (bnds : (ident * ctype) list) (c: state -> 'a * circuit) : 'a * circuit = 
      let st' = open_circ_lambda st bnds in
      let x, (c, inps) = c st' in
      x, (c, (List.hd st'.lambdas) @ inps)

  end

  (* Inputs helper functions *)
  let merge_inputs (cs: cinp list) (ds: cinp list) : cinp list =
(*
    Format.eprintf "Comparing input lists: @.";
    List.iter (Format.eprintf "%a " pp_cinp) cs;
    Format.eprintf "@.";
    List.iter (Format.eprintf "%a " pp_cinp) ds;
    Format.eprintf "@.";
*)
    if List.for_all2 (fun {id=id1; type_=ct1} {id=id2; type_=ct2} -> id1 = id2 && ct1 = ct2) cs ds then cs 
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
      | _ -> raise (CircError (Format.asprintf "Mismatched inputs:@\nInp1: %a@\nInp2: %a@\n" pp_cinp inp1 pp_cinp inp2))
    ) Map.empty target inps in
    fun inp -> Map.find_opt inp map

  (* Renames circuit2 inputs to match circuit 1 *)
  let unify_inputs (target: cinp list) ((c, inps): circuit) : circ = 
    let map_ = unify_inputs_renamer target inps in
    {c with reg = Backend.applys map_ c.reg}
    
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
  let circuit_tuple_proj (({reg = r; type_= CTuple tys}, inps): circuit) (i: int) =
    let idx, ty = List.takedrop i tys in
    let ty = List.hd ty in
    let idx = List.fold_left (+) 0 (List.map size_of_ctype idx) in
    {reg = (Backend.slice r idx (size_of_ctype ty)); type_ = ty}, inps

  let circuit_tuple_of_circuits (cs: circuit list) : circuit = 
    let tys = (List.map (fun (c : circuit) -> (fst c).type_) cs) in 
    let circ = Backend.flatten (List.map (fun (c : circuit) -> (fst c).reg) cs) in 
    let inps = List.snd cs in
    {reg = circ; type_= CTuple tys}, merge_inputs_list inps

  let circuits_of_circuit_tuple (({reg= tp; type_=CTuple szs}, tpinps) : circuit) : circuit list = 
    snd @@ List.fold_left_map 
      (fun idx ty -> 
        let sz = (size_of_ctype ty) in
        (idx + sz, 
        ({reg = (Backend.slice tp idx sz); type_ = ty}, tpinps)))
      0 szs 

  (* Convert a circuit's output to a given circuit type *)
  let convert_type (t: ctype) (({type_;_} as c, inps) as circ: circuit) : circuit = 
    match t, type_ with
    (* When types are the same, do nothing *)
    | (CArray {width=w; count=n}, CArray {width=w'; count=n'}) when w = w' && n = n' -> circ 
    | (CBitstring n, CBitstring n') when n = n' -> circ
    | (CTuple tys, CTuple tys') when List.for_all2 (=) tys tys' -> circ
    | (CBool, CBool) -> circ

    (* Bistring => Type conversions *)
    | (CArray {width=w; count=n}, CBitstring n') when w * n = n' -> { c with type_ = t }, inps 
    | (CTuple tys, CBitstring n) when List.sum @@ List.map size_of_ctype tys = n -> { c with type_ = t}, inps 
    | (CBool, CBitstring 1) -> { c with type_ = t}, inps 

    (* Type => Bitstring conversions *)
    | (CBitstring n, CArray {width=w'; count=n'}) when n = w' * n' -> { c with type_ = t}, inps
    | (CBitstring n, CTuple tys') when n = List.sum @@ List.map size_of_ctype tys' -> { c with type_ = t}, inps
    | (CBitstring 1, CBool) -> {c with type_ = t}, inps

    (* Fail on everything else *)
    | _ -> 
      raise (CircError (Format.asprintf "Failed to convert circuit %a of type %a to type %a@."
      pp_circ c pp_ctype type_ pp_ctype t))

  let can_convert_input_type (t1: ctype) (t2: ctype) : bool =
    size_of_ctype t1 = size_of_ctype t2     

  let convert_input_types ((c, inps) : circuit) (tys: ctype list) : circuit = 
    let exception IncompatibleTypes in
    c, List.map2 (fun inp ty ->
      if can_convert_input_type inp.type_ ty then
        { inp with type_ = ty }
      else raise IncompatibleTypes
    ) inps tys

  (* Input Helper Functions *)
  (* FIXME: maybe change name from inp -> input? *)
  let new_cbool_inp ?(name = `Str "input") () : circ * cinp = 
    let id, inp = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_node ~id 0
    | `Idn idn -> let id = tag idn in
      id, Backend.input_node ~id 0
    | `Bad -> 
      -1, Backend.bad
    in
    { reg = Backend.reg_of_node inp; type_= CBool }, { type_ = CBool; id; }

  let new_cbitstring_inp ?(name = `Str "input") (sz: int) : circ * cinp =
    let id, r = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_of_size ~id sz
    | `Idn idn -> let id = tag idn in
      id, Backend.input_of_size ~id sz
    | `Bad -> 
      -1, Backend.bad_reg sz 
    in
    { reg = r; type_ = CBitstring sz},
    { type_ = CBitstring sz; id; }

  (* TODO: maybe remove? *)
  let new_cbitstring_inp_reg ?name (sz: int) : flatcirc * cinp =
    let c, inp = new_cbitstring_inp ?name sz in
    (c.reg, inp)

  let new_carray_inp ?(name = `Str "input") (el_sz: int) (arr_sz: int) : circ * cinp = 
    let id, arr = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_of_size ~id (el_sz * arr_sz) 
    | `Idn idn -> let id = tag idn in
      id, Backend.input_of_size ~id (el_sz * arr_sz) 
    | `Bad -> 
      -1, Backend.bad_reg (el_sz * arr_sz) 
    in
    { reg = arr; type_ = CArray {width=el_sz; count=arr_sz}}, 
    { type_ = CArray {width=el_sz; count=arr_sz}; id; } 

  let new_ctuple_inp ?(name = `Str "input") (tys: ctype list) : circ * cinp =
    let id, tp = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
    id, Backend.input_of_size ~id (List.sum @@ List.map size_of_ctype tys)
    | `Idn idn -> let id = tag idn in
    id, Backend.input_of_size ~id (List.sum @@ List.map size_of_ctype tys)
    | `Bad ->
      -1, Backend.bad_reg (List.sum @@ List.map size_of_ctype tys)
    in
    { reg = tp; type_ = CTuple tys},
    { type_ = CTuple tys; id; }

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

  let circuit_true  = {reg = Backend.reg_of_node Backend.true_; type_=CBool}, [] 
  let circuit_false  = {reg = Backend.reg_of_node Backend.false_; type_=CBool}, [] 

  let circuit_and ((c, cinps): circuit) ((d, dinps): circuit) =  
    if c.type_ = d.type_ then
      { reg = Backend.land_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      raise (CircError "Cannot logical and circuits of different types ")

  let circuit_or ((c, cinps): circuit) ((d, dinps): circuit) = 
    if c.type_ = d.type_ then
      { reg = Backend.lor_ c.reg d.reg; type_ = c.type_ }, merge_inputs cinps dinps
    else
      raise (CircError "Cannot logical or circuits of different types ")

  let circuit_not ((c, cinps): circuit) =
    {c with reg = Backend.lnot_ c.reg}, cinps

  let circuit_is_free (f: circuit) : bool = List.is_empty @@ snd f 

  let circuit_ite ~(c: circuit) ~(t: circuit) ~(f: circuit) : circuit =
    assert ((circuit_is_free t) && (circuit_is_free f) && (circuit_is_free c));
    let c = match (fst c).type_ with
    | CBool -> Backend.node_of_reg (fst c).reg
    | _ -> assert false
    in
    let res_r = Backend.reg_ite c (fst t).reg (fst f).reg in
    match ((fst t).type_, (fst f).type_) with
    | CBitstring nt, CBitstring nf when nt = nf -> {reg = res_r; type_ = (fst t).type_}, []   
    | CArray {width=wt; count=nt}, CArray {width=wf; count=nf} when wt = wf && nt = nf -> {reg = res_r; type_ = (fst t).type_}, []  
    | CTuple szs_t, CTuple szs_f when List.all2 (=) szs_t szs_f -> {reg = res_r; type_ = (fst t).type_}, [] 
    | CBool, CBool -> {reg = res_r; type_ = (fst t).type_}, []
    | _ -> raise (CircError (Format.asprintf "Invalid arguments for circuit_ite (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_ctype) (List.map (fun (c: circuit) -> (fst c).type_) [t; f])))

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
    | _ -> raise (CircError (Format.asprintf "Invalid arguments for circuit_eq (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_ctype) (List.map (fun (c : circuit) -> (fst c).type_) [c; d])))

  (* Ignore types, do extensionally over bits, return the circuits evaluating to the condition *)
  let circuit_eqs ((c, cinps): circuit) ((d, dinps): circuit) : circuit list = 
    let inps = merge_inputs cinps dinps in
    assert (size_of_ctype c.type_ = size_of_ctype d.type_);
    let cs = Backend.node_list_of_reg c.reg in
    let ds = Backend.node_list_of_reg d.reg in
    List.map2 (fun c d ->
      let r = Backend.node_eq c d |> Backend.reg_of_node in
      {reg = r; type_ = CBool}, inps) cs ds

    
  let circuit_compose (c: circuit) (args: circuit list) : circuit = 
    (let exception InputIncompatible in
      try
        if not (List.for_all2 (fun c cinp -> circuit_input_compatible c cinp) args (snd c)) then raise InputIncompatible;
    with 
      InputIncompatible -> 
        if debug then Format.eprintf "Error on application:@\nTarget:%a@\n@[<hov 2>Args:%a@]@\n"
        pp_circuit c
        (fun fmt cs -> List.iter (Format.fprintf fmt "%a@\n" pp_circuit) cs) args;
        raise (CircError "Failed to compose circuits")
    | Invalid_argument _ -> raise (CircError (Format.asprintf "Bad number of arguments to circuit (expected: %d, got: %d)" (List.length (snd c)) (List.length args))));
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

  (* Circuit Lambda functions *)

    (* Functions for dealing with uninitialized inputs *)
  let circuit_uninit (t: ctype) : circuit = 
    match t with
    | CTuple szs ->
      let ctp, cinp = new_ctuple_inp ~name:`Bad szs in
      ((ctp, []) :> circuit)
    | CArray {width=el_sz; count=arr_sz} ->
      let carr, cinp = new_carray_inp ~name:`Bad el_sz arr_sz in
      ((carr, []) :> circuit)
    | CBitstring sz ->
      let c, cinp = new_cbitstring_inp ~name:`Bad sz in
      ((c, []) :> circuit)
    | CBool ->
      let c, inp = new_cbool_inp ~name:`Bad () in
      ((c, []) :> circuit)
    
  let circuit_has_uninitialized (c: circuit) : int option =
    Backend.have_bad (fst c).reg

  let circ_equiv ?(pcond:circuit option) ((c1, inps1): circuit) ((c2, inps2): circuit) : bool = 
(*     let () = if debug then Format.eprintf "c1: %a@\nc2: %a@\n" pp_circuit  (c1, inps1) pp_circuit (c2, inps2) in *)
    let pcond = Option.map (convert_type CBool) pcond in (* Try to convert to bool *) (* FIXME: duplicated check *)
    let pcc = match pcond with
    | Some ({reg = b; type_ = CBool}, pcinps) -> 
        Backend.apply (unify_inputs_renamer inps1 pcinps) (Backend.node_of_reg b)
    | None -> Backend.true_ 
    | _ -> raise (CircError "non bool input for circuit equiv precondition") 
    in
    (* TODO: add code to check that inputs match *)
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
    if debug then Format.eprintf "Calling circ_sat on circuit: %a@." pp_circuit (c, inps);
    let c = match c with 
    | {type_ = CBool; reg} -> Backend.node_of_reg reg
    | _ -> raise (CircError "Cannot apply circ_sat on a non bool circuit")
    in
    let inps = List.map (function 
      | { type_ = CBool; id } -> (id, 1)
      | { type_ = CBitstring w; id } -> (id, w) 
      | { type_ = CArray {width=w1; count=w2}; id } -> (id, w1*w2)
      | { type_ = CTuple tys; id } -> (id, List.sum @@ List.map size_of_ctype tys) 

    ) inps in
    Backend.sat ~inps c 
    
  let circ_taut ((c, inps): circuit) : bool = 
    if debug then Format.eprintf "Calling circ_taut on circuit: %a@." pp_circuit (c, inps);
    let c = match c with 
    | {type_ = CBool; reg} -> Backend.node_of_reg reg
    | _ -> raise (CircError "Cannot apply circ_sat on a non bool circuit")
    in
    let inps = List.map (function 
      | { type_ = CBool; id } -> (id, 1)
      | { type_ = CBitstring w; id } -> (id, w) 
      | { type_ = CArray {width=w1; count=w2}; id } -> (id, w1*w2)
      | { type_ = CTuple tys; id } -> (id, List.sum @@ List.map size_of_ctype tys) 

    ) inps in
    Backend.taut ~inps c 

  (* Dependency analysis related functions. These assume one input/output and all bitstring types *)
  (* For more complex circuits, we might be able to simulate this with a int -> (int, int) map *)
  let is_decomposable (in_w: width) (out_w: width) ((r, inps) as c: circuit) : bool = 
    match r, inps with
    | {type_= CBitstring w; reg = r}, {type_=CBitstring w'} :: [] when (w mod out_w = 0) ->
      let deps = Backend.Deps.deps_of_reg r in
      Backend.Deps.is_splittable in_w out_w deps &&
      let base, top = Backend.Deps.dep_range deps in
      let () = if debug then Format.eprintf "Passed backend check, checking width of deps (top - base = %d | in_w = %d)@." (top - base) in_w in
      (top - base) mod in_w = 0
    | _ -> 
        if debug then Format.eprintf "Failed decomposition type check@\n";
        if debug then Format.eprintf "In_w: %d | Out_w : %d | Circ: %a" in_w out_w pp_circuit c;
        false

  (* TODO: Extend this for multiple inputs? *)
  let align_renamer ((r, inps) : circuit) : (int * int) * cinp * (Backend.inp -> Backend.inp option) = 
    begin match r.type_ with
    | CBitstring _ -> ()
    | _ -> assert false (* TODO: FIXME *)
    end;
    match inps with 
    | [{type_ = CBitstring w; id}] ->
      let d = Backend.Deps.deps_of_reg r.reg in
      assert (Backend.Deps.single_dep d);
      let (start_idx, end_idx) as range = Backend.Deps.dep_range d in
      range, 
      {type_ = CBitstring (end_idx - start_idx); id},
      (fun (id_, w) ->
        if id <> id_ then None else
        if w < start_idx || w >= end_idx then None
        else Some (id_, w - start_idx))
    | _ -> raise (CircError "Failed to rename inputs in align_renamer")

  let align_inputs ((c, inps): circuit) (slcs: (int * int) option list) : circuit =
    assert (List.compare_lengths inps slcs = 0);
    let alignment = List.combine slcs inps in
    let inps = List.map 
    (function
    | None, inp -> inp
    | Some (sz, offset), ({type_ = CBitstring w_} as inp) ->
      {inp with type_ = CBitstring sz}
    | Some (sz, offset), ({type_ = CArray {width=w; count=n}} as inp) ->
      assert (sz mod w = 0);
      {inp with type_ = CArray {width=w; count=sz / w}}
    | _ -> raise (CircError "Failed to align inputs") 
    ) alignment
    in
    let aligners = 
      List.map
      (function 
      | None, _ -> fun (id_, w) -> None
      | Some (sz, offset), {id} ->
      (fun (id_, w) ->
        if debug then Format.eprintf "Aligning id=%d w=%d offset=%d sz=%d@." id_ w offset sz;
        if id <> id_ then None else
        if w < offset || w >= offset + sz then Some Backend.bad
        else Some (Backend.input_node ~id (w - offset)))
      ) alignment
    in
    let aligner = List.fold_left (fun f1 f2 ->
      fun inp -> match f1 inp with
      | Some _ as res -> res
      | None -> f2 inp
    ) (fun (id_, w) -> None) aligners
    in
    {c with reg = Backend.applys aligner c.reg}, inps

  (* Inputs mean different things depending on circuit type *)
  (* FIXME PR: maybe differentiate the two functions ? *)
  let circuit_slice ~(size:int) ((c, inps): circuit) (offset: int) : circuit =
    assert (size >= 0);
    assert (offset >= 0);
    match c.type_ with 
    | CArray {width=w; count=n} when size mod w = 0 && offset mod w = 0 -> {reg = Backend.slice c.reg offset size; type_ = CArray {width=w; count=size}}, inps
    | CArray _ -> raise (CircError "Bad array slice")
    | CBitstring w -> 
        { reg =  (Backend.slice c.reg offset size); type_ = CBitstring size}, inps
    | CTuple tys ->
        assert (List.length tys >= offset + size);
        let offset, tys = List.takedrop offset tys in
        let offset = List.sum @@ List.map size_of_ctype offset in
        let tys = (List.take size tys) in 
        let sz = List.sum @@ List.map size_of_ctype tys in
        {reg = (Backend.slice c.reg offset sz); type_ = CTuple tys}, inps
    | CBool -> 
        raise (CircError "Cannot slice boolean circuit")

  (* Does not type check *)
  let circuit_slice_insert ((orig_c, orig_inps): circuit) (idx: int) ((new_c, new_inps): circuit) : circuit = 
    { orig_c with reg = (Backend.insert orig_c.reg idx new_c.reg)}, merge_inputs orig_inps new_inps

  let split_renamer (n: count) (in_w: width) (inp: cinp) : (cinp array) * (Backend.inp -> Backend.node option) =
    match inp with
    | {type_ = CBitstring w; id} when w mod in_w = 0 ->
        let ids = Array.init n (fun i -> create ("split_" ^ (string_of_int i)) |> tag) in
        Array.map (fun id -> {type_ = CBitstring in_w; id}) ids, 
        (fun (id_, w) -> 
          if id <> id_ then None else
          let id_idx, bit_idx = (w / in_w), (w mod in_w) in
          Some (Backend.input_node ~id:ids.(id_idx) bit_idx))
    | {type_ = CBitstring w; id}  ->
        if debug then Format.eprintf "Failed to build split renamer for n=%d in_w=%d w=%d@." n in_w w; 
        raise (CircError "Failed to rename during split")
    | _ -> raise (CircError "Failed to rename during split")

  let check_decomp_inputs ((c, inps): circuit) : bool = 
    begin match c.type_ with
    | CBitstring _ -> ()
    | _ -> assert false (* TODO: FIXME *)
    end;
    let inps = List.map (function
      | {type_ = CBitstring w; id} -> 
        (id, w)
      | _ -> raise (CircError "Cannot apply mapreduce with more than one input") 
    ) inps in
    Backend.Deps.check_inputs c.reg inps


  (* 
     Takes a circuit and uses dependency analysis to separate it into 
     subcircuits corresponding to the output bits
     
     In particular, equivalence between two circuits is equivalent 
     to equivalence between the subcircuits 

     Implicitly flattens everything to bitstrings
  *)
  let fillet_circuit ((c, inps) : circuit) : circuit list = 
    let r = c.reg |> Backend.node_list_of_reg in
    List.map (fun n ->
      let new_inps = List.map (fun {id;type_} ->
        {id=EcIdent.create "_" |> tag; type_}) inps 
      in
      let renamings = List.combine 
        (List.map (fun {id} -> id) inps)
        (List.map (fun {id} -> id) new_inps)
      |> List.to_seq |> Map.of_seq 
      in
      let renamings = fun v -> Map.find_opt v renamings in
      let n', shifts = Backend.Deps.excise_bit ~renamings n in

      let new_inps = List.filter_map (fun {id;type_} ->
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


(*
  let fillet_circuit ((c, inps) : circuit) : circuit list = 
    let rec collapse (acc: Backend.node list) (cur, d: Backend.node * Backend.Deps.dep) (cs: (Backend.node * Backend.Deps.dep) list) : Backend.node list =
      match cs with 
      | [] -> (cur::acc)
      | (c, d')::cs -> 
        if debug && false then Format.eprintf "Comparing deps:@.%a@.To deps:@.%a@."
        Backend.Deps.pp_dep d 
        Backend.Deps.pp_dep d';
        if d = d' then 
        collapse acc ((Backend.band cur c), d) cs
        else
        collapse (cur::acc) (c, d') cs
    in


    let r = c.reg |> Backend.node_list_of_reg in
    let nbits = List.length r in
(*     let r = List.take nbits r in *)
    

    let r = List.map (fun n ->
      n, Backend.Deps.dep_of_node n) r in

    let r = match r with
    | [] -> []
    | n::ns -> collapse [] n ns
    in

    Format.eprintf "%d bits after collapsing (from %d initial)@." (List.length r) nbits;


    let r = List.map Backend.Deps.excise_bit r in
    let n1, s1 = List.hd r in
    List.iteri (fun i (n, s) ->
      Format.eprintf "Comparing node 0 to node %d => " i;
      if Backend.nodes_eq n n1 then
        Format.eprintf "Structurally equal@."
      else 
        Format.eprintf "Structurally different@."
    ) r; assert false
    
*)


  (* Batches circuit checks by dependencies. Assumes equivalent checks are contiguous *)
  let batch_checks ?(sort = true) (checks: circuit list) : circuit list =
    (* Order by dependencies *)
    let checks = if sort then begin 

    let checks = List.map (fun (c, inps) ->
      (c, inps), Backend.(Deps.dep_of_node (node_of_reg c.reg))) checks in
    let checks = List.stable_sort (fun (_, d1) (_, d2) ->
      let m1 = (Map.keys d1 |> Set.of_enum |> Set.min_elt) in
      let m2 = (Map.keys d2 |> Set.of_enum |> Set.min_elt) in
      let c1 = Int.compare m1 m2 in
      if c1 = 0 then
        Int.compare (Map.find m1 d1 |> Set.min_elt) (Map.find m1 d2 |> Set.min_elt)
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
        if debug && false then Format.eprintf "Comparing deps:@.%a@.To deps:@.%a@."
        Backend.Deps.pp_dep d 
        Backend.Deps.pp_dep d';
        if d = d' then 
        doit acc ((circuit_and cur c), d) cs
        else
        doit (cur::acc) (c, d') cs
    in

    match checks with
    | [] -> []
    | c::cs -> doit [] c cs

   

  (* Assumes all the pre and post have been split, takes all the pres and one post *) 
  let fillet_taut (pres: (circuit * Backend.Deps.dep) list) ((post_circ, post_inps): circuit) : bool =
    assert (List.for_all (fun ((_c, inps), _) -> inps = post_inps) pres);
    assert (List.for_all (fun (({type_;reg}, _), _) -> type_ = CBool) pres);
    assert (post_circ.type_ = CBool);
    let d = Backend.(Deps.dep_of_node (node_of_reg post_circ.reg)) in
    let compat_pres = List.filteri (fun i (c, pre_dep) ->
      Backend.Deps.dep_contained pre_dep d
    ) pres in
    let compat_pres = List.fst compat_pres in
    let node_post = Backend.node_of_reg post_circ.reg in
    let nodes_pre = List.map (fun (c, _) -> Backend.node_of_reg c.reg) compat_pres in
    let node_post, shifts = Backend.Deps.excise_bit node_post in
    let inps = List.map (fun {id; type_} ->
      let low, hi = Map.find id shifts in
      {id; type_ = CBitstring (hi - low + 1)}
    ) post_inps in
    let inp_map = fun (id, v) ->
      match Map.find_opt id shifts with
      | Some (min, max) -> 
          let new_id =  v - min in
          assert (new_id <= max);
          Some (id, v - min)
      | None -> assert false
    in
    let nodes_pre = Backend.Deps.rename_inputs inp_map (Backend.reg_of_node_list nodes_pre) in
    let pre = List.fold_left Backend.band Backend.true_ (Backend.node_list_of_reg nodes_pre) |> Backend.reg_of_node in
    let pre = {reg = pre; type_ = CBool}, inps in
    let post = Backend.reg_of_node node_post in
    let post = {reg = post; type_ = CBool}, inps in
    let cond = circuit_or (circuit_not pre) post in
    circ_taut cond

  (* 
    - Attaches preconditions to postconditions
    - Realigns inputs
    - Checks for structural equality of circuits
    - SMT check for any remainings ones
   *)
  let fillet_tauts (pres: circuit list) (posts: circuit list) : bool =
    (* Remove structurally equal circuits *)
    (* FIXME: not working because you have to 0 align everything before *)
    (* Assumes everything is single bit outputs *)
    let rec collapse (acc: circuit list) (cur: circuit) (cs: circuit list) : circuit list = 
      match cs with
      | [] -> cur::acc
      | (({reg;_}, _) as c)::cs ->
        let n', _ = Backend.node_of_reg reg |> Backend.Deps.excise_bit in
        let n, _ = Backend.node_of_reg (fst cur).reg |> Backend.Deps.excise_bit in
        if Backend.nodes_eq n n' then
          (if debug then Format.eprintf "Collapsing circuit@.";
          collapse acc cur cs)
        else 
          (if debug then Format.eprintf "Not collapsing circuit@.";
          collapse (cur::acc) c cs)
    in

    match posts with
    | [] -> true
    | post::posts ->
      assert (List.for_all (fun ({type_;reg}, _) -> type_ = CBool) pres);
      assert (List.for_all (fun ({type_;reg}, _) -> type_ = CBool) posts);
      let posts = collapse [] post posts in
      if debug then Format.eprintf "%d conditions to check after structural equality collapse@." (List.length posts);
      let pres = List.map (fun ((c, _) as circ) -> circ,
        Backend.Deps.dep_of_node (Backend.node_of_reg c.reg)) pres in
      List.iteri (fun i post -> 
        if debug then Format.eprintf "Checking equivalence for bit %d@." i; (* FIXME *)
        assert (fillet_taut pres post)) posts;
      true
   

  (* General Mapreduce Procedure:
     Assumes: 
       Input bits start from 0
     Input: 
       Circuit: One Bitstring Input => One Bitstring Output
       Lane Descriptions: Output Bit List/Set/Array /\ Input Bit Set
     Output: 
       Circuit List: One circuit for each lane, inputs renamed to be sequential
     Throws:
       CircuitError 
       | -> When lane outputs do not fully cover circuit
       | -> When lane dependency description does not fit circuit
     *)
  let general_decompose (r: circ) (inp: cinp) (lanes: ((int list) * (int Set.t)) list): circuit list = 
    let exception DependencyError in
    (* Check that outputs cover the circuit *)
    let outputs = List.fst lanes |> List.flatten |> List.sort (Int.compare) in
    assert (List.for_all2 (fun a b -> a = b) outputs (List.init (List.length outputs) (fun i -> i)));

    (* Separate one lane *)
    let doit ((outputs, inputs): int list * int Set.t) : circuit =
      let c = Backend.subcirc r.reg outputs in
      if not @@ Backend.Deps.forall_inputs (fun id b -> 
        inp.id = id && 
        Set.mem b inputs) c then raise DependencyError;
      let _, new_inp = new_cbitstring_inp (Set.cardinal inputs) in
      let bit_renames = List.mapi (fun i b -> (b, i)) (Set.to_list inputs) in
      let bit_renamer = Map.of_seq (List.to_seq bit_renames) in
      let renamer (id, b) = 
        if id = inp.id then
          Option.map (fun new_b -> (new_inp.id, new_b)) (Map.find_opt b bit_renamer)
        else None
      in {reg = (Backend.Deps.rename_inputs renamer c); type_ = CBitstring (Backend.size_of_reg c)}, [new_inp]
      (* A FIXME A *)
    in
    try List.map doit lanes 
    with DependencyError -> 
      raise (CircError "dep_check_general_decompose")

  let decompose (in_w: width) (out_w: width) ((c, inps): circuit) : circuit list = 
    let n = Backend.size_of_reg c.reg in
    assert (n mod out_w = 0);
    let n_lanes = n / out_w in
    let inp = match inps with
    | ({type_ = CBitstring n'; id} as inp)::[] when n' mod in_w = 0 && n' / in_w = n_lanes -> inp
    | _ -> raise (CircError "bad inputs in circ for mapreduce")
    in
    let lanes = List.map (fun i -> List.init out_w (fun j -> i*out_w + j), Set.of_list (List.init in_w (fun j -> i*in_w + j))) (List.init n_lanes (fun i -> i)) in
    try general_decompose c inp lanes
    with CircError _ ->
      let d = Backend.Deps.block_deps_of_reg out_w c.reg in
      Format.eprintf "Dependencies:@.%a@." Backend.Deps.pp_block_deps d;
      raise (CircError "Split dependency check failed")


  (* FIXME: different things based on input or just fix bitstrings? *)
  let permute (w: width) (perm: (int -> int)) ((r, inps): circuit) : circuit =
    begin match r.type_ with
    | CBitstring _ -> ()
    | _ -> assert false (* TODO: FIXME *)
    end;
    assert false; {r with reg = (Backend.permute w perm r.reg)}, inps

  let compute ~(sign: bool) ((r, inps) as c: circuit) (args: arg list) : zint option = 
    begin match r.type_ with
    | CBitstring _ -> ()
    | _ -> assert false (* TODO: FIXME *)
    end;

    if List.compare_lengths args inps <> 0 
      then raise (CircError (Format.asprintf "Bad number of arguments for compute (expected: %d, got: %d)" (List.length inps) (List.length args)));
    let args = List.map2i (fun i arg inp ->
    match arg, inp with
    | `Circuit c, inp when circuit_input_compatible c inp -> c
    | `Constant i, {type_ = CBitstring size} -> { reg = (Backend.reg_of_zint ~size i); type_ = CBitstring size}, []
    | _ -> raise (CircError (Format.asprintf "Arg mismatch at index %d, (arg: %a, inp: %a)" i pp_arg arg pp_cinp inp))
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
    | _, _::_ -> raise (CircError ("Non constant circuit in compute after arg application"))
    | _ -> raise (CircError ("Got non-bitstring type in compute"))

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

  let circuit_to_file ~(name: string) ((c, inps) as circ : circuit) : symbol =
    match c, inps with
    | {reg = r; type_ = CBitstring _}, {type_ = CBitstring w; id}::[] -> (* TODO: rename inputs? *)
      Backend.reg_to_file ~input_count:w ~name (Backend.applys (fun (id_, i) -> if id_ = id then Some (Backend.input_node ~id:0 (i+1)) else None) r)
    | _ -> raise (CircError (Format.asprintf "Unsupported circuit for output (%a), only one bitstring input one bitstring output supported@." pp_circuit circ))

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
      let circuit_of_parametric_bvop (op: EcDecl.crb_bvoperator) (args: arg list) : circuit =
      match op with 
      | { kind = `ASliceGet (((_, Some n), (_, Some w)), (_, Some m)) } -> 
        begin match args with 
        (* Assume type checking from EC? *)
        | [ `Circuit (({type_ = CArray _}, _) as circ) ; `Constant i ] ->
          begin
            match (fst circ).type_ with
            | CArray {width=w'; count=n'} when  n' = n && w = w' -> 
              circuit_slice ~size:m ({reg = (fst circ).reg; type_ = CBitstring (w' * n')}, (snd circ)) (to_int i)
            | CArray {width=w'; count=n'} -> 
              raise (CircError (Format.asprintf "Bad array size in asliceget (expected (%d, %d), got (%d, %d))" n w n' w'))
            | _ -> assert false (* Does not happen, guarded by match above *)
          end
        | args -> 
          raise (CircError (Format.asprintf "Bad arguments for asliceget, expected (arr, idx), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | { kind = `ASliceSet (((_, Some n), (_, Some w)), (_, Some m)) } -> 
        begin match args with 
        | [ `Circuit (({type_ = CArray _}, _) as arr_circ) ; `Constant i ; `Circuit (({type_ = CBitstring _}, _) as bs_circ) ] ->
          begin match (fst arr_circ).type_, (fst bs_circ).type_ with
          | CArray {width=w'; count=n'}, CBitstring m' when n' = n && w' = w && m = m' ->
            circuit_slice_insert arr_circ (to_int i) bs_circ 
          | ct1, ct2 -> raise (CircError (Format.asprintf "Bad sizes in asliceget (expected arr=(%d, %d) bs=(%d), got (%a, %a))" n w m pp_ctype ct1 pp_ctype ct2))
        end 
        | args -> 
          raise (CircError (Format.asprintf "Bad arguments for asliceset, expected (arr, idx, bitstring), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end

      (* FIXME: what do we want for out of bounds extract? Decide later *)
      | { kind = `Extract ((_, Some w_in), (_, Some w_out)) } -> 
        begin match args with
        | [ `Circuit (({type_ = CBitstring _}, _ ) as c) ; `Constant i ] ->
          circuit_slice ~size:w_out c (to_int i) 
        | _ -> raise (CircError (Format.asprintf "Bad arguments for extract, expected (bitstring, idx), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | { kind = `Insert ((_, Some w_orig), (_, Some w_ins)) } -> 
        begin match args with
        | [ `Circuit (({type_ = CBitstring _}, _) as orig_c) ; `Constant i ; `Circuit (({ type_=CBitstring _}, _) as new_c) ] ->
            (circuit_slice_insert orig_c (to_int i) new_c :> circuit)
        | _ -> raise (CircError (Format.asprintf "Bad arguments for insert, expected (orig_bs, idx, new_bs), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end

      | { kind = `Map ((_, Some w_i), (_, Some w_o), (_, Some n)) } -> 
        begin match args with 
        | [ `Circuit (({ type_=CBitstring _}, [{type_=CBitstring w_i'}; _]) as cf); `Circuit ({reg = arr; type_ = CArray {width=w_i''; count=n_i''}}, arr_inps) ] when (w_i' = w_i && w_i'' = w_i') && (n_i''  = n) ->
          let circs, inps = List.split @@ List.map (fun c -> 
            match circuit_compose cf [c] with
            | { type_ = CBitstring _; reg}, inps -> reg, inps 
            | c, _ -> raise (CircError (Format.asprintf "Bad return from map, expected bitstring, got %a" pp_circ c))
            ) 
          (List.init n (fun i -> {reg = (Backend.slice arr (i*w_i) w_i); type_ = CBitstring w_i}, []))
          in
          (assert (List.for_all ((=) (List.hd inps)) inps));
          let inps = List.hd inps in
          let circ = { reg = (Backend.flatten circs); type_ = CArray {width=w_o; count=n}} in  
          (circ, inps) 
        | args -> raise (CircError (Format.asprintf "Bad arguments for map, expected (lane_f, arr), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | { kind = `Get (_, Some w_in) } -> 
        begin match args with
        | [ `Circuit ({reg = bs; type_ = CBitstring _}, cinps); `Constant i ] ->
          {type_ = CBool; reg = Backend.reg_of_node (Backend.get bs (to_int i))}, cinps
        | _ -> raise (CircError (Format.asprintf "Bad arguments for get, expected (bs, idx), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | { kind = `AInit ((_, Some n), (_, Some w_o)) } -> 
        begin match args with
        | [ `Init init_f ] -> 
          let circs, cinps = List.split @@ List.init n init_f in
          let circs = List.map 
            (function 
              | {type_ = CBitstring _; reg = r} when Backend.size_of_reg r = w_o -> r 
            | ret -> raise (CircError (Format.asprintf "Bad return for init_fun, expected bitstring, got (%a)" pp_circ ret))) 
          circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          {type_ = CArray {width=w_o; count=n} ; reg = Backend.flatten circs}, cinps 
        | _ -> raise (CircError (Format.asprintf "Bad arguments for ainit, expected (init_fun), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | { kind = `Init (_, Some w) } -> 
        begin match args with 
        | [ `Init init_f ] ->
          let circs, cinps = List.split @@ List.init w init_f in
          let circs = List.map 
            (function 
            | {type_ = CBool; reg = b} -> Backend.node_of_reg b 
            | ret -> raise (CircError (Format.asprintf "Bad return for init_fun, expected bitstring, got (%a)" pp_circ ret))) circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          {type_ = CBitstring w; reg = (Backend.reg_of_node_list circs)}, cinps
        | _ -> raise (CircError (Format.asprintf "Bad arguments for init, expected (init_fun), got (%a)" Format.(pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") pp_arg) args))
        end
      | _ -> assert false (* Should not happen because calls should be guarded by call to op_is_parametric_bvop *)


      let circuit_of_bvop (op: EcDecl.crb_bvoperator) : circuit = 
      match op with
      | { kind = `Add (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.add c1 c2 )}, [inp1; inp2] 

      | { kind = `Sub (_, Some size) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.sub c1 c2)}, [inp1; inp2] 

      | { kind = `Mul  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.mul c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.udiv c1 c2)}, [inp1; inp2] 

      | { kind = `Div ((_, Some size), true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.sdiv c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.umod c1 c2)}, [inp1; inp2] 

      | { kind = `Rem ((_, Some size), true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.smod c1 c2)}, [inp1; inp2] 
        (* Should this be mod or rem? TODO FIXME*)

      | { kind = `Shl  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.lshl c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.lshr c1 c2)}, [inp1; inp2] 

      | { kind = `Shr  ((_, Some size), true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.ashr c1 c2)}, [inp1; inp2] 

      | { kind = `Shls  ((_, Some size1), (_, Some size2)) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size1 in 
        let c2, inp2 = new_cbitstring_inp_reg size2 in
        {type_ = CBitstring size1; reg = (Backend.lshl c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size1 in 
        let c2, inp2 = new_cbitstring_inp_reg size2 in
        {type_ = CBitstring size1; reg = (Backend.lshr c1 c2)}, [inp1; inp2] 

      | { kind = `Shrs  ((_, Some size1), (_, Some size2), true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size1 in 
        let c2, inp2 = new_cbitstring_inp_reg size2 in
        {type_ = CBitstring size1; reg = (Backend.ashr c1 c2)}, [inp1; inp2] 

      | { kind = `Rol  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.rol c1 c2)}, [inp1; inp2] 

      | { kind = `Ror  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.ror c1 c2)}, [inp1; inp2] 

      | { kind = `And  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.land_ c1 c2)}, [inp1; inp2] 

      | { kind = `Or   (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.lor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Xor  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBitstring size; reg = (Backend.lxor_ c1 c2)}, [inp1; inp2] 

      | { kind = `Not  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        {type_ = CBitstring size; reg = (Backend.lnot_ c1)}, [inp1] 

      | { kind = `Opp  (_, Some size) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        {type_ = CBitstring size; reg = (Backend.opp c1)}, [inp1] 

      | { kind = `Lt ((_, Some size), false) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.ult c1 c2)}, [inp1; inp2] 
      
      | { kind = `Lt ((_, Some size), true) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.slt c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), false) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.ule c1 c2)}, [inp1; inp2] 

      | { kind = `Le ((_, Some size), true) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        {type_ = CBool; reg = Backend.reg_of_node (Backend.sle c1 c2)}, [inp1; inp2] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), false) } ->
        (* assert (size <= out_size); *)
        let c1, inp1 = new_cbitstring_inp_reg size in 
        {type_ = CBitstring out_size; reg = (Backend.uext c1 out_size)}, [inp1] 

      | { kind = `Extend ((_, Some size), (_, Some out_size), true) } ->
        (* assert (size <= out_size); *)  
        let c1, inp1 = new_cbitstring_inp_reg size in 
        {type_ = CBitstring out_size; reg = (Backend.sext c1 out_size)}, [inp1] 

      | { kind = `Truncate ((_, Some size), (_, Some out_sz)) } ->
        (* assert (size >= out_sz); *)
        let c1, inp1 = new_cbitstring_inp_reg size in
        {type_ = CBitstring out_sz; reg = (Backend.trunc c1 out_sz)}, [inp1] 

      | { kind = `Concat ((_, Some sz1), (_, Some sz2), (_, Some szo)) } ->
        (* assert (sz1 + sz2 = szo); *)
        let c1, inp1 = new_cbitstring_inp_reg sz1 in 
        let c2, inp2 = new_cbitstring_inp_reg sz2 in
        {type_ = CBitstring szo; reg = (Backend.concat c1 c2)}, [inp1; inp2] 

      | { kind = `A2B (((_, Some w), (_, Some n)), (_, Some m))} ->
        (* assert (n * w = m); *)
        let c1, inp1 = new_carray_inp w n in  
        {c1 with type_ = CBitstring m}, [inp1] 

      | { kind = `B2A ((_, Some m), ((_, Some w), (_, Some n)))} ->
        (* assert (n * w = m); *)
        let c1, inp1 = new_cbitstring_inp m in
        {c1 with type_ = CArray {width=w; count=n}}, [inp1] 

      | { kind = `ASliceGet _ | `ASliceSet _ | `Extract _ | `Insert _ | `Map _ | `AInit _ | `Get _ | `Init _  } 
      | _ 
      -> assert false (* Should be guarded by call to op_is_bvop *)

      (* | _ -> raise @@ CircError "Failed to generate op"  *)
    end

    module ArrayOps = struct
      let array_get (({reg = c; type_ = CArray {width=w; count=n}}, inps) : circuit) (i: int) : circuit = 
        try 
          { type_ = CBitstring w; reg = (Backend.slice c (i*w) w)}, inps  
        with Invalid_argument _ ->
          raise (CircError (Format.asprintf "Bad index for bitstring get (expected < %d, got %d)" Backend.(size_of_reg c) i))

      let array_set (({reg = arr; type_ =  CArray {width=w; count=n}}, inps) : circuit) (pos: int) (({reg = bs; type_ = CBitstring w'}, cinps): circuit) : circuit =
        let exception SizeMismatch in
        try
          assert (w = w');
          { type_ = CArray {width=w; count=n}; reg = (Backend.insert arr (pos * w) bs)},
          merge_inputs inps cinps
        with Invalid_argument _ -> 
          raise (CircError (Format.asprintf "Bad index for bitstring set (expected < %d, got %d)" n pos))
        | SizeMismatch -> 
          raise (CircError (Format.asprintf "Array set size mismatch (expected: %d, got: %d)" w (Backend.size_of_reg bs)))

    (* FIXME: review this functiono | FIXME: Not axiomatized in QFABV.ec file *)
      let array_oflist (circs : circuit list) (dfl: circuit) (len: int) : circuit =
        let circs, inps = List.split circs in
        let dif = len - List.length circs in assert (dif >= 0);
  (*       if debug then Format.eprintf "Len, Dif in array_oflist: %d, %d@." len dif; *)
        let circs = circs @ (List.init dif (fun _ -> fst dfl)) in
        let inps = if dif > 0 then inps @ [snd dfl] else inps in
        let circs = List.map 
          (function 
            | {type_ = CBitstring _; reg = r} -> r
            | list_elem -> raise (CircError (Format.asprintf "Bad circuit type for list element in array of_list, expected bitstring got %a" pp_circ list_elem))
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
