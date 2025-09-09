open EcBigInt
open EcUtils
open EcSymbols
open EcDecl
open EcIdent

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

let debug : bool = false

let specifications : (string, Lospecs.Ast.adef) Map.t Lazy.t =
  Lazy.from_fun (fun () ->
    let specs_avx2 = Filename.concat (List.hd Lospecs.Config.Sites.specs) "avx2.spec" in
    let specs_avx2 = C.load_from_file ~filename:specs_avx2 in
    let specs_armv7 = Filename.concat (List.hd Lospecs.Config.Sites.specs) "armv7.spec" in
    let specs_armv7 = C.load_from_file ~filename:specs_armv7 in
    let specs = specs_armv7 @ specs_avx2 in
    Map.of_seq (List.to_seq specs)
  )

let get_specification_by_name (name : string) : Lospecs.Ast.adef option =
  let lazy specifications = specifications in
  Map.find_opt name specifications

(* Backend implementing minimal functions needed for the translation *)
(* Minimal expected functionality is QF_ABV *)
(* Input are: some identifier + some bit *)
module type CBackend = sig
  type node (* Corresponds to a single output node *)
  type reg
  (* Id + offset, both assumed starting at 0 *)
  type inp = int * int

  exception NonConstantCircuit (* FIXME: Rename later *)

  val true_ : node
  val false_ : node

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
    type deps
    type block_deps

    val deps_of_reg : reg -> deps
    val block_deps_of_deps : int -> deps -> block_deps 
    val block_deps_of_reg : int -> reg -> block_deps

    val pp_deps : Format.formatter -> deps -> unit
    val pp_block_deps : Format.formatter -> block_deps -> unit

    (* Assumes only one reg -> reg and parallel blocks *)
    val is_splittable : int -> int -> deps -> bool

    val are_independent : block_deps -> bool

    val single_dep : deps -> bool
    (* Assumes single_dep *)
    val dep_range : deps -> int * int
    (* Checks if all the deps are in a given list of inputs *)
    val check_inputs : reg -> (int * int) list -> bool

    val forall_inputs : (int -> int -> bool) -> reg -> bool
    val rename_inputs : ((int * int) -> (int * int) option) -> reg -> reg
  end
end

module LospecsBack : CBackend = struct
  type node = C.node
  type reg = C.node array
  type inp = int * int

  exception NonConstantCircuit (* FIXME: Rename later *)

  let true_ = C.true_
  let false_ = C.false_
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
    Array.of_list (C.of_bigint_all ~size (to_zt v))

  let bool_array_of_reg (r: reg) : bool array = 
    Array.map (fun r -> 
      match (r :> C.node) with 
      | { gate = False; id } when id > 0 -> false
      | { gate = False; id } when id < 0 -> true
      | _ -> raise NonConstantCircuit 
    ) r

  let bool_list_of_reg (r: reg) : bool list = 
    List.init (Array.length r) (fun i -> 
      match r.(i) with 
      | { gate = False; id } when id > 0 -> false
      | { gate = False; id } when id < 0 -> true
      | _ -> raise NonConstantCircuit
    )

  let szint_of_reg (r: reg) : zint = 
    bool_list_of_reg r |> C.sbigint_of_bools |> of_zt 

  let uzint_of_reg (r: reg) : zint = 
    bool_list_of_reg r |> C.ubigint_of_bools |> of_zt
    
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
    BWZ.circ_equiv ?inps (node_list_of_reg r1) (node_list_of_reg r2) pcond  

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
    let args = List.map node_list_of_reg args in
    reg_of_node_list (C.circuit_of_specification args def)

  (* SMTLib Base Ops *)
  let add (r1: reg) (r2: reg) : reg = C.add_dropc (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let sub (r1: reg) (r2: reg) : reg = C.sub_dropc (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let mul (r1: reg) (r2: reg) : reg = C.umull (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let udiv (r1: reg) (r2: reg) : reg = C.udiv (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let sdiv (r1: reg) (r2: reg) : reg = C.sdiv (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  (* FIXME: mod or rem here? *)
  let umod (r1: reg) (r2: reg) : reg  = C.umod (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let smod (r1: reg) (r2: reg) : reg = C.smod (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let lshl (r1: reg) (r2: reg) : reg = C.shift ~side:`L ~sign:`L (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let lshr (r1: reg) (r2: reg) : reg = C.shift ~side:`R ~sign:`L  (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let ashr (r1: reg) (r2: reg) : reg = C.shift ~side:`R ~sign:`A  (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let rol (r1: reg) (r2: reg) : reg = C.rol (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let ror (r1: reg) (r2: reg) : reg = C.ror (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let land_ (r1: reg) (r2: reg) : reg = C.land_ (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let lor_ (r1: reg) (r2: reg) : reg = C.lor_ (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let lxor_ (r1: reg) (r2: reg) : reg = C.lxor_ (Array.to_list r1) (Array.to_list r2) |> Array.of_list
  let lnot_ (r1: reg) : reg  = C.lnot_ (Array.to_list r1) |> Array.of_list
  let ult (r1: reg) (r2: reg) : node = C.ugt (Array.to_list r2) (Array.to_list r1) 
  let slt (r1: reg) (r2: reg) : node = C.sgt (Array.to_list r2) (Array.to_list r1)
  let ule (r1: reg) (r2: reg) : node = C.uge (Array.to_list r2) (Array.to_list r1)
  let sle (r1: reg) (r2: reg) : node = C.sge (Array.to_list r2) (Array.to_list r1)
  let uext (r1: reg) (size: int) : reg = C.uextend ~size (Array.to_list r1) |> Array.of_list
  let sext (r1: reg) (size: int) : reg = C.sextend ~size (Array.to_list r1) |> Array.of_list
  let trunc (r1: reg) (size: int) : reg = Array.sub r1 0 size  
  let concat (r1: reg) (r2: reg) : reg = Array.append r1 r2 
  let flatten (rs: reg list) : reg = Array.concat rs

  let reg_to_file ~(input_count: int) ?(inp_name_map: (int -> string) option) ~(name: string) (r: reg) : symbol =
    C.write_aiger_bin_temp ~input_count ?inp_name_map ~name (node_list_of_reg r)

  module Deps = struct 
    type dep = (int, int Set.t) Map.t
    type deps = dep array
    type block_deps = (int * dep) array

    let deps_of_reg = fun r -> HL.deps (node_list_of_reg r)
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
      | _ -> 
        (if debug then Format.eprintf "Failed first check@\n"; 
        if debug then Format.eprintf "Map keys: ";
        if debug then Array.iteri (fun i dep ->
          Format.eprintf "Bit %d: " i;
          List.iter (Format.eprintf "%d") (Map.keys dep |> List.of_enum);
          Format.eprintf "@\n") d;
        assert false)
        

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

    let forall_inputs (check: int -> int -> bool) (r: reg) : bool =
      let d = deps_of_reg r in
      Array.for_all (fun d -> 
        Map.for_all (fun id bs -> Set.for_all (check id) bs) d) 
      d

    let rename_inputs (renamer: (int * int) -> (int * int) option) (r: reg) : reg =
      C.maps (fun (id, b) -> 
        Option.map (fun (id, b) -> input_node ~id b) (renamer (id, b)) 
      ) (node_list_of_reg r) |> (reg_of_node_list)

  end
end

module type CircuitInterface = sig
  type carray_type
  type cbitstring_type
  type ctuple_type
  type cbool_type
  type cbool = [`CBool of cbool_type ]
  type carray = [`CArray of carray_type ]
  type cbitstring = [`CBitstring of cbitstring_type ]
  type ctuple = [`CTuple of ctuple_type ]
  type circ = [cbool | carray | cbitstring | ctuple ]
  type ctype = [`CArray of (int * int) | `CBitstring of int | `CTuple of int list | `CBool ]
  type cinp = {
    type_ : ctype;
    id: int
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 
  
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

  module PState : sig
    type pstate

    val update_pstate : pstate -> symbol -> circuit -> pstate
    val pstate_get_opt : pstate -> symbol -> circuit option
    val pstate_get : pstate -> symbol -> circuit 
    val pstate_get_all : pstate -> (symbol * circuit) list
    val empty_pstate : pstate
    val map_pstate : (symbol -> circuit -> circuit) -> pstate -> pstate
  end

  module LocalCache : sig
    type cache
    val update_cache : cache -> ident -> circuit -> cache
    val cache_get : cache -> ident -> circuit
    val cache_add : cache -> ident -> circuit -> cache
    val empty_cache : cache
    val cache_map : (ident -> circuit -> circuit) -> cache -> cache
  end

  module BVOps : sig
    val circuit_of_bvop : EcDecl.crb_bvoperator -> circuit  
    val circuit_of_parametric_bvop : EcDecl.crb_bvoperator -> arg list -> circuit
  end

  module ArrayOps : sig
      val array_get : carray cfun -> int -> circuit
      val array_set : carray cfun -> int -> cbitstring cfun -> circuit 
      val array_oflist : circuit list -> circuit -> int -> circuit 
  end

  (* Circuit type utilities *)
  val size_of_ctype : ctype -> int
  val ctype_of_circ : circ -> ctype
  val convert_output : ctype -> circuit -> circuit 
  val can_convert_input_type : ctype -> ctype -> bool

  (* Pretty Printers *)
  val pp_ctype : Format.formatter -> ctype -> unit
  val pp_cinp : Format.formatter -> cinp -> unit
  val pp_circ : Format.formatter -> circ -> unit
  val pp_circuit : Format.formatter -> circuit -> unit

  (* General utilities *)
  val cbitstring_of_zint : size:int -> zint -> cbitstring
  val circ_of_zint : size:int -> zint -> circ
  val cbitstring_cfun_of_zint : size:int -> zint -> cbitstring cfun
  val circuit_of_zint : size:int -> zint -> circuit 

  (* Type conversions *)
  val cbool_of_circuit : ?strict:bool -> circuit -> cbool * cinp list
  val cbitstring_of_circuit : ?strict:bool -> circuit -> cbitstring * cinp list
  val carray_of_circuit : ?strict:bool -> circuit -> carray * cinp list
  val ctuple_of_circuit : ?strict:bool -> circuit -> ctuple * cinp list

  (* Type constructors *)
  val new_cbool_inp : ?name:[`Str of string | `Idn of ident] -> cbool * cinp
  val new_cbitstring_inp : ?name:[`Str of string | `Idn of ident] -> int -> cbitstring * cinp
  val new_carray_inp : ?name:[`Str of string | `Idn of ident] -> int -> int -> carray * cinp
  val new_ctuple_inp : ?name:[`Str of string | `Idn of ident] -> int list -> ctuple * cinp

  (* Aggregation functions *)
  val circuit_aggregate : circuit list -> circuit
  val circuit_aggregate_inputs : circuit -> circuit

  (* Circuits representing booleans *)
  val circuit_true : cbool cfun 
  val circuit_false : cbool cfun 
  val circuit_and : cbool cfun -> cbool cfun -> cbool cfun
  val circuit_or  : cbool cfun -> cbool cfun -> cbool cfun
  val circuit_not : cbool cfun -> cbool cfun

  (* <=> circuit has not inputs (every input is unbound) *)
  val circuit_is_free : circuit -> bool
  
  (* Direct circuuit constructions *)
  val circuit_ite : c:(cbool * (cinp list)) -> t:circuit -> f:circuit -> circuit
  val circuit_eq : circuit -> circuit -> cbool cfun


  (* Circuit tuples *)
  val circuit_tuple_proj : (ctuple * (cinp list)) -> int -> (cbitstring * (cinp list)) 
  val circuit_tuple_of_circuits : (cbitstring * (cinp list)) list -> (ctuple * (cinp list))
  val circuits_of_circuit_tuple : (ctuple * (cinp list)) -> (cbitstring * (cinp list)) list

  (* Circuit lambdas, for managing inputs *)
  val open_circ_lambda : (ident * ctype) list -> circuit list 
  val open_circ_lambda_cache : LocalCache.cache -> (ident * ctype) list -> LocalCache.cache 
  val open_circ_lambda_pstate : PState.pstate -> (ident * ctype) list -> PState.pstate 
  val close_circ_lambda : (ident * ctype) list -> circuit -> circuit 
  val close_circ_lambda_cache : LocalCache.cache -> (ident * ctype) list -> LocalCache.cache 
  val close_circ_lambda_pstate : PState.pstate -> (ident * ctype) list -> PState.pstate 

  (* Avoid nodes for uninitialized inputs *)
  val circuit_uninit : ctype -> circuit
  val circuit_has_uninitialized : circuit -> int option

  (* Logical reasoning over circuits *)
  val circ_equiv : ?pcond:(cbool * (cinp list)) -> circuit -> circuit -> bool
  val circ_sat   : circuit -> bool 
  val circ_taut  : circuit -> bool 

  (* Composition of circuit functions, should deal with inputs and call some backend *)
  val circuit_compose : circuit -> circuit list -> circuit

  (* Computing the function given by a circuit *)
  val compute : sign:bool -> cbitstring cfun -> arg list -> zint option

  (* Mapreduce/Dependecy analysis related functions *)
  val is_decomposable : int -> int -> cbitstring cfun -> bool
  val decompose : int -> int -> cbitstring cfun -> (cbitstring cfun) list
  val permute : int -> (int -> int) -> cbitstring cfun -> cbitstring cfun
  val align_inputs : circuit -> (int * int) option list -> circuit
  val circuit_slice : size:int -> circuit -> int -> circuit
  val circuit_slice_insert : cbitstring cfun -> int -> cbitstring cfun -> cbitstring cfun

  (* Wraps the backend call to deal with args/inputs *) 
  val circuit_to_file : name:string -> circuit -> symbol

  val circuit_from_spec : ?name:symbol -> (ctype list * ctype) -> Lospecs.Ast.adef -> circuit
end

module MakeCircuitInterfaceFromCBackend(Backend: CBackend) : CircuitInterface = struct
  (* Module Types *)
  type count = int
  type width = int
  type carray_type = Backend.reg * width 
  type cbitstring_type = Backend.reg
  type ctuple_type = Backend.reg * (width list)
  type cbool_type = Backend.node
  type carray = [`CArray of carray_type ]
  type cbool = [`CBool of cbool_type ]
  type cbitstring = [`CBitstring of cbitstring_type ]
  type ctuple = [`CTuple of ctuple_type ]
  type circ = [cbool | carray | cbitstring | ctuple]
  type ctype = [
    `CArray of (width * count) 
  | `CBitstring of width 
  | `CTuple of width list 
  | `CBool]
  type cinp = {
    type_ : ctype;
    id : int;
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 

  (* Helper functions *)
  let (|->) ((a,b)) ((f,g)) = (f a, g b)
  let idnt = fun x -> x

  let cbitstring_of_zint ~(size: int) (i: zint) : cbitstring = 
    `CBitstring (Backend.reg_of_zint ~size i)
  let circ_of_zint ~(size: int) (i: zint) : circ = 
    (cbitstring_of_zint ~size i :> circ)
  let cbitstring_cfun_of_zint ~(size: int) (i: zint) : cbitstring cfun = 
    cbitstring_of_zint ~size i, []
  let circuit_of_zint ~(size: int) (i: zint) : circuit =
    (cbitstring_cfun_of_zint ~size i :> circuit)

  (* Pretty printers *)
  let pp_ctype (fmt: Format.formatter) (t: ctype) : unit = 
    match t with
    | `CArray (w, n)  -> Format.fprintf fmt "Array(%d@%d)" n w 
    | `CBool -> Format.fprintf fmt "Bool"
    | `CTuple szs -> Format.fprintf fmt "Tuple(%a)" (Format.pp_print_list ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ") Format.pp_print_int) szs
    | `CBitstring w -> Format.fprintf fmt "Bitstring@%d" w

  let pp_cinp (fmt: Format.formatter) (inp: cinp) : unit = 
    Format.fprintf fmt "Input(id: %d, type = %a)" inp.id pp_ctype inp.type_

  let pp_circ (fmt : Format.formatter) (c: circ) : unit =
    match c with
    | `CArray (r, w) -> Format.fprintf fmt "Circ(Array[%d@%d])" (Backend.size_of_reg r) w
    | `CBitstring r -> Format.fprintf fmt "Circ(Bitstring[%d])" (Backend.size_of_reg r)
    | `CTuple (_, ws) -> Format.fprintf fmt "Circ(Tuple(%a))" (fun fmt szs ->
        Format.fprintf fmt "%d" (List.hd szs); List.iter (Format.fprintf fmt ", %d") (List.tl szs)) ws
    | `CBool _ -> Format.fprintf fmt "Circ(Bool)"
    
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

  (* PSTATE DEFINIITION *)
  module PState = struct
    type pstate = (symbol, circuit) Map.t

    let update_pstate pstate v c =
      Map.add v c pstate

    let pstate_get_opt (pstate: pstate) (v: symbol) : circuit option = 
        Map.find_opt v pstate  
    let pstate_get (pstate: pstate) (v: symbol) : circuit = 
      let res = pstate_get_opt pstate v in
      try
        Option.get res 
      with Invalid_argument _ ->
        raise (CircError (Format.sprintf "No circuit in state for name %s (Uninitalized variable?)@." v))

    let pstate_get_all (pstate: pstate) : (symbol * circuit) list = 
      Map.enum pstate |> List.of_enum

    let empty_pstate : pstate = Map.empty 

    let map_pstate : (symbol -> circuit -> circuit) -> pstate -> pstate =
      Map.mapi
  end
  open PState

  (* Inputs helper functions *)
  let merge_inputs (cs: cinp list) (ds: cinp list) : cinp list =
    (* FIXME: hack *)
    if cs = ds then cs 
    else cs @ ds

  let merge_inputs_list (cs: cinp list list) : cinp list =
    List.fold_right (merge_inputs) cs []

  let merge_circuit_inputs (c: circuit) (d: circuit) : cinp list =
    merge_inputs (snd c) (snd d)

  let unify_inputs_renamer (target: cinp list) (inps: cinp list) : Backend.inp -> cbool_type option =
    let map = List.fold_left2 (fun map inp1 inp2 -> match inp1, inp2 with
      | {type_ = `CBitstring w ; id=id_tgt},
        {type_ = `CBitstring w'; id=id_orig} when w = w' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init w (fun i -> i))
      | {type_ = `CArray (w , n ); id=id_tgt},
        {type_ = `CArray (w', n'); id=id_orig} when w = w' && n = n' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w*n) (fun i -> i))
      | {type_ = `CTuple szs ; id=id_tgt},
        {type_ = `CTuple szs'; id=id_orig} when szs = szs' -> 
          let w = List.sum szs in
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w) (fun i -> i))
      | {type_ = `CBool; id=id_tgt},
        {type_ = `CBool; id=id_orig} ->
          Map.add (id_orig, 0) (Backend.input_node ~id:id_tgt 0) map
      | _ -> if debug then Format.eprintf "Mismatched inputs:@\nInp1: %a@\nInp2: %a@\n" pp_cinp inp1 pp_cinp inp2; assert false 
    ) Map.empty target inps in
    fun inp -> Map.find_opt inp map

  (* Renames circuit2 inputs to match circuit 1 *)
  let unify_inputs (target: cinp list) ((c2, inps2): 'a cfun) : 'a = 
    let map_ = unify_inputs_renamer target inps2 in
    let circ = match c2 with
    | `CBitstring r -> `CBitstring (Backend.applys map_ r)
    | `CArray (r,w) -> `CArray (Backend.applys map_ r, w)
    | `CTuple (r, szs) -> `CTuple (Backend.applys map_ r, szs)
    | `CBool b -> `CBool (Backend.apply map_ b)
    in
    circ 

  let circuit_input_compatible ?(strict = false) ((c, _): circuit) (cinp: cinp) : bool =
    match c, cinp with
    | `CBitstring r, { type_ = `CBitstring w } when Backend.size_of_reg r = w -> true
    | `CArray (r, w), { type_ = `CArray (w', n)} when Backend.size_of_reg r = w'*n && w = w' -> true
    | `CTuple (r, szs), { type_ = `CTuple szs' } when szs = szs' -> true
    | `CBool _, { type_ = `CBool } -> true
    | `CBool _, { type_ = `CBitstring 1 } when not strict -> true
    | `CBitstring r, { type_ = `CBool } when not strict && Backend.size_of_reg r = 1 -> true
    | _ -> false

  (* Type conversions *)
  let reg_of_circ (c: circ) : Backend.reg = 
    match c with
    | `CTuple (r, _) | `CArray (r, _) 
    | `CBitstring r -> r 
    | `CBool r -> Backend.reg_of_node r 

  let cbool_of_circuit ?(strict : bool = false) (c: circuit) : (cbool * (cinp list)) = 
    match (fst c) with
    | `CArray (r, _) | `CTuple (r, _) | `CBitstring r 
      when (not strict) && Backend.size_of_reg r = 1 
        -> `CBool (Backend.node_of_reg r), snd c
    | `CBool _ as r -> (r, snd c) 
    | _ -> assert false

  let cbitstring_of_circuit ?(strict : bool = false) (c: circuit) : (cbitstring * (cinp list)) =
    match (fst c) with
    | `CArray (r, _) | `CTuple (r, _) 
      when not strict -> `CBitstring r, snd c
    | `CBitstring _ as r -> (r, snd c)
    | `CBool r -> (`CBitstring (Backend.reg_of_node r), snd c)
    | _ -> assert false

  (* FIXME: is this a good convetion? *)
  let carray_of_circuit ?(strict : bool = false) (c: circuit) : (carray * (cinp list)) =
    match (fst c) with
    | `CArray _ as r -> r, snd c
    | `CTuple (r, _ ) | `CBitstring r 
      when not strict -> `CArray (r, Backend.size_of_reg r), snd c
    | `CBool r when not strict -> `CArray (Backend.reg_of_node r, 1), snd c
    | _ -> assert false

  let ctuple_of_circuit ?(strict : bool = false) (c: circuit) : (ctuple * (cinp list)) =
    match (fst c) with
    | `CArray (r, _) | `CBitstring r 
      when not strict -> `CTuple (r, [ Backend.size_of_reg r ]), snd c
    | `CTuple _ as r -> r, snd c
    | `CBool r when not strict -> `CTuple (Backend.reg_of_node r, [ 1 ]), snd c
    | _ -> assert false

  (* Circuit tuples *)
  let circuit_tuple_proj ((`CTuple (r, ws)), inps: ctuple * (cinp list)) (i: int) =
    let idx, w = List.takedrop i ws in
    let w = List.hd w in
    let idx = List.fold_left (+) 0 idx in
    `CBitstring (Backend.slice r idx w), inps

  let circuit_tuple_of_circuits (cs: (cbitstring * (cinp list)) list) : ctuple * (cinp list) = 
    let lens = List.map (fun (`CBitstring r) -> Backend.size_of_reg r) (List.fst cs) in 
    let circ = Backend.flatten @@ List.map (fun (`CBitstring r, _) -> r) cs in 
    let inps = List.snd cs in
    `CTuple (circ, lens) , merge_inputs_list inps

  let circuits_of_circuit_tuple ((`CTuple (tp, szs), tpinps) : (ctuple * cinp list)) : (cbitstring * cinp list) list = 
    snd @@ List.fold_left_map 
      (fun idx sz -> 
        (idx + sz, 
        (`CBitstring (Backend.slice tp idx sz), tpinps)))
      0 szs 

  let size_of_ctype (t: ctype) : int = 
    match t with 
    | `CBitstring n -> n
    | `CArray (n, w) -> n*w
    | `CTuple szs -> List.sum szs
    | `CBool -> 1

  let ctype_of_circ (c: circ) : ctype = 
    match c with
    | `CArray (r, w) -> 
      let n = Backend.size_of_reg r in
      assert (n mod w = 0);
      let n = n / w in
      `CArray (w, n)
    | `CTuple (r, szs) ->
      assert (Backend.size_of_reg r = List.sum szs);
      `CTuple szs
    | `CBitstring r -> `CBitstring (Backend.size_of_reg r)
    | `CBool _ -> `CBool

  (* Convert a circuit's output to a given circuit type *)
  let convert_output (t: ctype) ((c, inps) as circ: circuit) : circuit = 
    match t, c with
    (* When types are the same, do nothing *)
    | (`CArray (w', n), `CArray (r, w)) when (w' = w && Backend.size_of_reg r = w * n) -> circ 
    | (`CBitstring w, `CBitstring r) when (Backend.size_of_reg r = w) -> circ
    | (`CTuple szs', `CTuple (r, szs)) when (List.for_all2 (=) szs' szs) -> circ
    | (`CBool, `CBool _) -> circ

    (* Bistring => Type conversions *)
    | (`CArray (w', n), `CBitstring r) when (Backend.size_of_reg r = w'*n) -> `CArray (r, w'), inps 
    | (`CTuple szs', `CBitstring r) when List.sum szs' = Backend.size_of_reg r -> `CTuple (r, szs'), inps 
    | (`CBool, `CBitstring r) -> (cbool_of_circuit circ :> circuit)

    (* Type => Bitstring conversions *)
    | (`CBitstring n, `CArray (r, w)) when Backend.size_of_reg r = n -> `CBitstring r, inps
    | (`CBitstring n, `CTuple (r, szs)) when Backend.size_of_reg r = n -> `CBitstring r, inps
    | (`CBitstring 1, `CBool b) -> `CBitstring (Backend.reg_of_node b), inps

    (* Fail on everything else *)
    | _ -> 
        Format.eprintf "Failed to convert circuit %a of type %a to type %a@."
        pp_circ c pp_ctype (ctype_of_circ c) pp_ctype t;
        assert false (* FIXME: Error handling *)

  let can_convert_input_type (t1: ctype) (t2: ctype) : bool =
    size_of_ctype t1 = size_of_ctype t2     

  let convert_input_types ((c, inps) : circuit) (tys: ctype list) : circuit = 
    let exception IncompatibleTypes in
    c, List.map2 (fun inp ty ->
      if can_convert_input_type inp.type_ ty then
        { inp with type_ = ty }
      else raise IncompatibleTypes
    ) inps tys

  (* CACHE DEFINIITION *)
  (*type cache  = (ident, (cinput * circuit)) Map.t*)
  module LocalCache = struct
    type cache = (ident, circuit) Map.t
    let update_cache (cache: cache) (id: ident) (c: circuit) : cache = 
      Map.add id c cache
      
    let cache_get (cache: cache) (idn: ident) : circuit = 
      try 
        Map.find idn cache  
      with Not_found -> 
        assert false (* FIXME: Error handling *)

    let cache_add (cache: cache) (idn: ident) (c: circuit) : cache = 
      Map.add idn c cache 

    let empty_cache : cache = 
      Map.empty

    let cache_map : (ident -> circuit -> circuit) -> cache -> cache =
      Map.mapi
  end
  open LocalCache

  (* Input Helper Functions *)
  (* FIXME: maybe change name from inp -> input? *)
  let new_cbool_inp ?(name = `Str "input") : cbool * cinp = 
    let id, inp = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_node ~id 0
    | `Idn idn -> let id = tag idn in
      id, Backend.input_node ~id 0
    | `Bad -> 
      -1, Backend.bad
    in
    `CBool inp, { type_ = `CBool; id; }

  let new_cbitstring_inp ?(name = `Str "input") (sz: int) : cbitstring * cinp =
    let id, r = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_of_size ~id sz
    | `Idn idn -> let id = tag idn in
      id, Backend.input_of_size ~id sz
    | `Bad -> 
      -1, Backend.bad_reg sz 
    in
    `CBitstring r, 
    { type_ = `CBitstring sz; id; }

  let new_cbitstring_inp_reg ?name (sz: int) : cbitstring_type * cinp =
    let c, inp = new_cbitstring_inp ?name sz in
    (reg_of_circ (c :> circ), inp)

  let new_carray_inp ?(name = `Str "input") (el_sz: int) (arr_sz: int) : carray * cinp = 
    let id, arr = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.input_of_size ~id (el_sz * arr_sz) 
    | `Idn idn -> let id = tag idn in
      id, Backend.input_of_size ~id (el_sz * arr_sz) 
    | `Bad -> 
      -1, Backend.bad_reg (el_sz * arr_sz) 
    in
    `CArray (arr, el_sz), 
    { type_ = `CArray (el_sz, arr_sz); id; } 

  let new_ctuple_inp ?(name = `Str "input") (szs: int list) : ctuple * cinp =
    let id, tp = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
    id, Backend.input_of_size ~id (List.sum szs)
    | `Idn idn -> let id = tag idn in
    id, Backend.input_of_size ~id (List.sum szs)
    | `Bad ->
      -1, Backend.bad_reg (List.sum szs)
    in
    `CTuple (tp, szs),
    { type_ = `CTuple szs;
      id; }

  let circuit_true  = `CBool Backend.true_ , [] 
  let circuit_false = `CBool Backend.false_, []

  let circuit_and (`CBool c1, inps1) (`CBool c2, inps2) = 
    `CBool (Backend.band c1 c2), merge_inputs inps1 inps2 

  let circuit_or (`CBool c1, inps1) (`CBool c2, inps2) = 
    `CBool (Backend.bor c1 c2), merge_inputs inps1 inps2 

  let circuit_not (`CBool c, inps) =
    `CBool (Backend.bnot c), inps 

  let circuit_is_free (f: circuit) : bool = List.is_empty @@ snd f 

  let circuit_ite ~(c: cbool * (cinp list)) ~(t: circuit) ~(f: circuit) : circuit =
    assert ((circuit_is_free t) && (circuit_is_free f) && (circuit_is_free (c :> circuit)));
    let (`CBool c) = (fst c) in
    match (fst t, fst f) with
    | `CBitstring rt, `CBitstring rf -> (`CBitstring (Backend.reg_ite c rt rf), [])   
    | `CArray (rt, wt), `CArray (rf, wf) when wt = wf -> (`CArray (Backend.reg_ite c rt rf, wt), []) 
    | `CTuple (rt, szs_t), `CTuple (rf, szs_f) when szs_t = szs_f -> (`CTuple (Backend.reg_ite c rt rf, szs_t), []) 
    | `CBool t, `CBool f -> (`CBool (Backend.node_ite c t f) , [])
    | _ -> assert false

  let circuit_eq (c: circuit) (d: circuit) : (cbool cfun) =  
    match c, d with
    | (`CArray (r1, _), inps1), (`CArray (r2, _), inps2) 
    | (`CTuple (r1, _), inps1), (`CTuple (r2, _), inps2) 
    | (`CBitstring r1, inps1), (`CBitstring r2, inps2) ->
        `CBool (Backend.reg_eq r1 r2), merge_inputs inps1 inps2 
    | _ -> assert false
    
  let circuit_compose (c: circuit) (args: circuit list) : circuit = 
    (try
      assert (List.for_all2 (fun c cinp -> circuit_input_compatible c cinp) args (snd c))
    with 
      Assert_failure _ -> 
        if debug then Format.eprintf "Error on application:@\nTarget:%a@\n@[<hov 2>Args:%a@]@\n"
        pp_circuit c
        (fun fmt cs -> List.iter (Format.fprintf fmt "%a@\n" pp_circuit) cs) args;
        assert false
    | Invalid_argument _ -> assert false);
    let map = List.fold_left2 (fun map {id} c -> Map.add id c map) Map.empty (snd c) (List.fst args) in
    let map_ (id, idx) = 
      let circ = Map.find_opt id map in
      Option.bind circ (fun c -> 
        match c with
        | `CArray (r, _) | `CTuple (r, _) | `CBitstring r -> 
          begin try
            Some (Backend.get r idx)
          with Invalid_argument _ -> None 
          end
        | `CBool b when idx = 0 -> Some b
        | _ -> None
      ) 
    in
    let circ = match (fst c) with
    | `CBool b -> `CBool (Backend.apply map_ b)
    | `CArray (r, w) -> `CArray (Backend.applys map_ r, w)
    | `CBitstring r -> `CBitstring (Backend.applys map_ r)
    | `CTuple (r, szs) -> `CTuple (Backend.applys map_ r, szs)
    in
    let inps = merge_inputs_list (List.snd args) in
    (circ, inps)

  (* Circuit Lambda functions *)

  (* FIXME: Maybe make this convert things that are typed as bool into tbool? *)
  let circ_lambda_one (idn: ident) (t: ctype) : cinp * circuit = 
    match t with
    | `CTuple szs ->
      let ctp, cinp = new_ctuple_inp ~name:(`Idn idn) szs in
      cinp, ((ctp, []) :> circuit)
    | `CBool ->
      let c, cinp = new_cbool_inp ~name:(`Idn idn) in
      cinp, ((c, []) :> circuit)
    | `CArray (el_sz, arr_sz) ->
      let c, cinp = new_carray_inp ~name:(`Idn idn) el_sz arr_sz in
      cinp, ((c, []) :> circuit)
    | `CBitstring sz ->
      let c, cinp = new_cbitstring_inp ~name:(`Idn idn) sz in
      cinp, ((c, []) :> circuit)
    
  let open_circ_lambda (vs: (ident * ctype) list) : circuit list = 
    List.map (fun (idn, t) -> snd @@ circ_lambda_one idn t) vs 
    
  let open_circ_lambda_cache (cache : cache) (vs : (ident * ctype) list) : cache = 
    List.fold_left (fun cache (idn, t) -> 
      update_cache cache idn @@ snd @@ circ_lambda_one idn t)
    cache vs 
    
  let open_circ_lambda_pstate (pstate : pstate) (vs: (ident * ctype) list) : pstate = 
    List.fold_left (fun pstate (idn, t) ->
      update_pstate pstate (name idn) @@ snd @@ circ_lambda_one idn t)
    pstate vs

  let close_circ_lambda (vs : (ident * ctype) list) (c: circuit) : circuit = 
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one idn t) vs) in
    (fst c, merge_inputs cinps (snd c))

  let close_circ_lambda_cache (cache : cache) (vs: (ident * ctype) list) : cache = 
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one idn t) vs) in
    cache_map (fun _ c -> (fst c, merge_inputs cinps (snd c))) cache 

  let close_circ_lambda_pstate (pstate : pstate) (vs: (ident * ctype) list) : pstate =  
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one idn t) vs) in
    map_pstate (fun _ c -> (fst c, merge_inputs cinps (snd c))) pstate

  (* Functions for dealing with uninitialized inputs *)
  let circuit_uninit (t: ctype) : circuit = 
    match t with
    | `CTuple szs ->
      let ctp, cinp = new_ctuple_inp ~name:`Bad szs in
      ((ctp, []) :> circuit)
    | `CArray (el_sz, arr_sz) ->
      let carr, cinp = new_carray_inp ~name:`Bad el_sz arr_sz in
      ((carr, []) :> circuit)
    | `CBitstring sz ->
      let c, cinp = new_cbitstring_inp ~name:`Bad sz in
      ((c, []) :> circuit)
    | `CBool ->
      let c, inp = new_cbool_inp ~name:`Bad in
      ((c, []) :> circuit)
    
  let circuit_has_uninitialized (c: circuit) : int option =
    match (fst c) with
    | `CBitstring r | `CArray (r, _) | `CTuple (r, _) ->
      Backend.have_bad r 
    | `CBool b -> 
      if Backend.has_bad b then Some 0 else None

  let circ_equiv ?(pcond:(cbool * cinp list) option) ((c1, inps1): circuit) ((c2, inps2): circuit) : bool = 
(*     let () = if debug then Format.eprintf "c1: %a@\nc2: %a@\n" pp_circuit  (c1, inps1) pp_circuit (c2, inps2) in *)
    let pcc = match pcond with
    | Some (`CBool b, pcinps) -> 
        Backend.apply (unify_inputs_renamer inps1 pcinps) b
    | None -> Backend.true_ 
    in
    (* TODO: add code to check that inputs match *)
    let c2 = unify_inputs inps1 (c2, inps2) in
    let inps = List.map (function 
      | { type_ = `CBool; id } -> (id, 1)
      | { type_ = `CBitstring w; id } -> (id, w) 
      | { type_ = `CArray (w1, w2); id } -> (id, w1*w2)
      | { type_ = `CTuple szs; id } -> (id, List.sum szs) 

    ) inps1 in
    match c1, c2 with
    | `CBitstring r1, `CBitstring r2 -> 
        Backend.equiv ~inps ~pcond:pcc r1 r2
    | `CArray (r1, w1), `CArray (r2, w2) when w1 = w2 ->
        Backend.equiv ~inps ~pcond:pcc r1 r2
    | `CTuple (r1, szs1), `CTuple (r2, szs2) when szs1 = szs2 ->
        Backend.equiv ~inps ~pcond:pcc r1 r2
    | `CBool b1, `CBool b2 ->
        Backend.equiv ~inps ~pcond:pcc (Backend.reg_of_node b1) (Backend.reg_of_node b2)
    | _ -> false

  let circ_sat (c: circuit) : bool =
    let `CBool c, inps = cbool_of_circuit ~strict:false c in
    let inps = List.map (function 
      | { type_ = `CBool; id } -> (id, 1)
      | { type_ = `CBitstring w; id } -> (id, w) 
      | { type_ = `CArray (w1, w2); id } -> (id, w1*w2)
      | { type_ = `CTuple szs; id } -> (id, List.sum szs) 

    ) inps in
    Backend.sat ~inps c 
    
  let circ_taut (c: circuit) : bool = 
    if debug then Format.eprintf "Calling circ_taut on circuit: %a@." pp_circuit c;
    let `CBool c, inps = cbool_of_circuit ~strict:false c in
    let inps = List.map (function 
      | { type_ = `CBool; id } -> (id, 1)
      | { type_ = `CBitstring w; id } -> (id, w) 
      | { type_ = `CArray (w1, w2); id } -> (id, w1*w2)
      | { type_ = `CTuple szs; id } -> (id, List.sum szs) 

    ) inps in
    Backend.taut ~inps c 

  (* Dependency analysis related functions. These assume one input/output and all bitstring types *)
  (* For more complex circuits, we might be able to simulate this with a int -> (int, int) map *)
  let is_decomposable (in_w: width) (out_w: width) ((`CBitstring r, inps) as c: cbitstring cfun) : bool = 
    match inps with
    | {type_=`CBitstring w} :: [] when (Backend.size_of_reg r mod out_w = 0) ->
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
  let align_renamer ((`CBitstring r, inps) : cbitstring cfun) : (int * int) * cinp * (Backend.inp -> Backend.inp option) = 
    match inps with 
    | [{type_ = `CBitstring w; id}] ->
      let d = Backend.Deps.deps_of_reg r in
      assert (Backend.Deps.single_dep d);
      let (start_idx, end_idx) as range = Backend.Deps.dep_range d in
      range, 
      {type_ = `CBitstring (end_idx - start_idx); id},
      (fun (id_, w) ->
        if id <> id_ then None else
        if w < start_idx || w >= end_idx then None
        else Some (id_, w - start_idx))
    | _ -> assert false

  let align_inputs ((c, inps): circuit) (slcs: (int * int) option list) : circuit =
    assert (List.compare_lengths inps slcs = 0);
    let alignment = List.combine slcs inps in
    let inps = List.map 
    (function
    | None, inp -> inp
    | Some (sz, offset), ({type_ = `CBitstring w_} as inp) ->
      {inp with type_ = `CBitstring sz}
    | Some (sz, offset), ({type_ = `CArray (w, n)} as inp) ->
      assert (sz mod w = 0);
      {inp with type_ = `CArray (w, sz / w)}
    | _ -> assert false
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
    match c with
    | `CBitstring r -> (`CBitstring (Backend.applys aligner r), inps)
    | `CArray (r, w) -> (`CArray (Backend.applys aligner r, w), inps)
    | `CTuple (r, ws) -> (`CTuple (Backend.applys aligner r, ws), inps)
    | `CBool b -> (`CBool (Backend.apply aligner b), inps)

  (* Inputs mean different things depending on circuit type *)
  let circuit_slice ~(size:int) ((c, inps): circuit) (offset: int) =
    assert (size >= 0);
    assert (offset >= 0);
    match c with 
    | `CArray (r, w) when size mod w = 0 && offset mod w = 0 -> `CArray (Backend.slice r offset size, w), inps
    | `CBitstring r -> 
        `CBitstring (Backend.slice r offset size), inps
    | `CTuple (r, szs) ->
        assert (List.length szs >= offset + size);
        let offset, szs = List.takedrop offset szs in
        let offset = List.sum offset in
        let szs = (List.take size szs) in 
        let sz = List.sum szs in
        `CTuple (Backend.slice r offset sz, szs), inps
    | `CBool b -> 
        if debug then Format.eprintf "Cannot slice boolean circuit@.";
        assert false
    | _ -> assert false

  let circuit_slice_insert ((`CBitstring orig_r, orig_inps): cbitstring cfun) (idx: int) ((`CBitstring new_r, new_inps): cbitstring cfun) : cbitstring cfun = 
    `CBitstring (Backend.insert orig_r idx new_r), merge_inputs orig_inps new_inps

  let split_renamer (n: count) (in_w: width) (inp: cinp) : (cinp array) * (Backend.inp -> cbool_type option) =
    match inp with
    | {type_ = `CBitstring w; id} when w mod in_w = 0 ->
        let ids = Array.init n (fun i -> create ("split_" ^ (string_of_int i)) |> tag) in
        Array.map (fun id -> {type_ = `CBitstring in_w; id}) ids, 
        (fun (id_, w) -> 
          if id <> id_ then None else
          let id_idx, bit_idx = (w / in_w), (w mod in_w) in
          Some (Backend.input_node ~id:ids.(id_idx) bit_idx))
    | {type_ = `CBitstring w; id}  ->
        if debug then Format.eprintf "Failed to build split renamer for n=%d in_w=%d w=%d@." n in_w w; 
        assert false
    | _ -> assert false

  let check_decomp_inputs ((`CBitstring r, inps): cbitstring cfun) : bool = 
    let inps = List.map (function
      | {type_ = `CBitstring w; id} -> 
        (id, w)
      | _ -> assert false
    ) inps in
    Backend.Deps.check_inputs r inps

  (* FIXME: what is the last return value for? *)
  let decompose (in_w: width) (out_w: width) ((`CBitstring r, inps) as c: cbitstring cfun) : cbitstring cfun list * (int * int) = 
    if not (is_decomposable in_w out_w c) then 
      let deps = Backend.Deps.block_deps_of_reg out_w r in
      if debug then Format.eprintf "Failed to decompose. in_w=%d out_w=%d Deps:@.%a" in_w out_w (Backend.Deps.pp_block_deps) deps;
      assert false 
    else
    let n = (Backend.size_of_reg r) / out_w in
    let blocks = Array.init n (fun i -> 
      Backend.slice r (i*out_w) out_w) in
(*     let range, cinp, aligner = align_renamer c in *)
    let cinp = (List.hd inps) in
    let cinps, renamer = split_renamer n in_w cinp in
(*     let renamer = fun i -> Option.bind (aligner i) renamer in  *)
    let res = Array.map2 (fun r inp ->
      let r = Backend.applys renamer r in
      (`CBitstring r, [inp])
    ) blocks cinps |> Array.to_list, (0,0)
    in
    if not (List.for_all check_decomp_inputs (fst res)) then assert false else
    res

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
  let general_decompose ((`CBitstring r): cbitstring) (inp: cinp) (lanes: ((int list) * (int Set.t)) list): cbitstring cfun list = 
    let exception DependencyError in
    (* Check that outputs cover the circuit *)
    let outputs = List.fst lanes |> List.flatten |> List.sort (Int.compare) in
    assert (List.for_all2 (fun a b -> a = b) outputs (List.init (List.length outputs) (fun i -> i)));

    (* Separate one lane *)
    let doit ((outputs, inputs): int list * int Set.t) : cbitstring cfun =
      let c = Backend.subcirc r outputs in
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
      in `CBitstring (Backend.Deps.rename_inputs renamer c), [new_inp]
    in
    try List.map doit lanes 
    with DependencyError -> 
      raise (CircError "dep_check_general_decompose")

  let decompose (in_w: width) (out_w: width) ((`CBitstring r as c, inps): cbitstring cfun) : cbitstring cfun list = 
    let n = Backend.size_of_reg r in
    assert (n mod out_w = 0);
    let n_lanes = n / out_w in
    let inp = match inps with
    | ({type_ = `CBitstring n'; id} as inp)::[] when n' mod in_w = 0 && n' / in_w = n_lanes -> inp
    | _ -> raise (CircError "bad inputs in circ for mapreduce")
    in
    let lanes = List.map (fun i -> List.init out_w (fun j -> i*out_w + j), Set.of_list (List.init in_w (fun j -> i*in_w + j))) (List.init n_lanes (fun i -> i)) in
    try general_decompose c inp lanes
    with CircError _ ->
      let d = Backend.Deps.block_deps_of_reg out_w r in
      Format.eprintf "Dependencies:@.%a@." Backend.Deps.pp_block_deps d;
      raise (CircError "Split dependency check failed")


  let permute (w: width) (perm: (int -> int)) ((`CBitstring r, inps): cbitstring cfun) : cbitstring cfun =
    `CBitstring (Backend.permute w perm r), inps

  let compute ~(sign: bool) ((`CBitstring r, inps) as c: cbitstring cfun) (args: arg list) : zint option = 
    if List.compare_lengths args inps <> 0 then assert false else
    let args = List.map2 (fun arg inp ->
    match arg, inp with
    | `Circuit c, inp when circuit_input_compatible c inp -> c
    | `Constant i, {type_ = `CBitstring size} -> `CBitstring (Backend.reg_of_zint ~size i), []
    | _ -> assert false
    ) args inps 
    in
    match circuit_compose c args with
    | `CBitstring r, [] -> 
      begin try 
        Some (if sign 
        then Backend.szint_of_reg r
        else Backend.uzint_of_reg r)
      with Backend.NonConstantCircuit -> None
      end
    | _ -> assert false

  let circuit_aggregate (cs: circuit list) : circuit =
    let inps = List.snd cs in
    let cs = List.map (fun c -> match cbitstring_of_circuit ~strict:false c with
    | `CBitstring r, _ -> r) cs in
    let c = Backend.flatten cs in
    let inps = merge_inputs_list inps in
    (`CBitstring c, inps)

  let input_aggregate_renamer (inps: cinp list) : cinp * (Backend.inp -> cbool_type option) =
    let new_id = create "aggregated" |> tag in
    let (size, map) = List.fold_left (fun (size, map) inp ->
      match inp with
      | { type_ = `CBitstring w; id} ->
        (size + w, Map.add id (size, w) map) 
      | { type_ = `CArray (w, n); id} ->
        (size + (w*n), Map.add id (size, w*n) map)
      | { type_ = `CTuple szs; id} ->
        let w = List.sum szs in
        (size + w, Map.add id (size, w) map)
      | { type_ = `CBool; id} ->
        (size + 1, Map.add id (size, 1) map)
      ) (0, Map.empty) inps
    in
    {type_ = `CBitstring size; id=new_id},
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
    match c with
    | `CBitstring r -> `CBitstring (Backend.applys renamer r), [inp]
    | `CArray (r, w) -> `CArray (Backend.applys renamer r, w), [inp]
    | `CTuple (r, szs) -> `CTuple (Backend.applys renamer r, szs), [inp]
    | `CBool b -> `CBool (Backend.apply renamer b), [inp]

  let circuit_to_file ~(name: string) ((c, inps) : circuit) : symbol =
    match c, inps with
    | `CBitstring r, {type_ = `CBitstring w; id}::[] -> (* TODO: rename inputs? *)
      Backend.reg_to_file ~input_count:w ~name (Backend.applys (fun (id_, i) -> if id_ = id then Some (Backend.input_node ~id:0 (i+1)) else None) r)
    | _ -> if debug then Format.eprintf "Unsupported circuit for output, only one input one output supported@."; assert false

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
    (`CBitstring c, inps) |> convert_output ret_ty

    module BVOps = struct
      let circuit_of_parametric_bvop (op:EcDecl.crb_bvoperator) (args: arg list) : circuit =
      match op with 
      | { kind = `ASliceGet ((n, w), m) } -> 
        begin match args with 
        (* Assume type checking from EC? *)
        | [ `Circuit ((`CArray _, _) as circ) ; `Constant i ] ->
          begin
            match ctype_of_circ (fst circ) with
            | `CArray (w', n') when  n' = n && w = w' -> 
              circuit_slice ~size:m (cbitstring_of_circuit ~strict:false circ :> circuit) (to_int i)
            | `CArray (w', n') -> 
            if debug then 
              Format.eprintf "Bad arguments for array slice get: w = %d@.%a@." 
                w 
                (fun fmt args -> List.iter (Format.fprintf fmt "%a@\n" CArgs.pp_arg) args) args;
                assert false
            | _ -> assert false
          end
        | args -> 
          if debug then Format.eprintf "Bad arguments for array slice get: w = %d@.%a@." w
          (fun fmt args -> List.iter (Format.fprintf fmt "%a@\n" pp_arg) args) args;
          assert false
        end
      | { kind = `ASliceSet ((n, w), m) } -> 
        begin match args with 
        | [ `Circuit ((`CArray _, _) as arr_circ) ; `Constant i ; `Circuit ((`CBitstring _, _) as bs_circ) ] ->
          begin match ctype_of_circ (fst arr_circ), ctype_of_circ (fst bs_circ) with
          | `CArray (w', n'), `CBitstring m' when n' = n && w' = w && m = m' ->
            let arr_c = cbitstring_of_circuit ~strict:false arr_circ in
            let bs_c = cbitstring_of_circuit ~strict:true bs_circ in
            let res_c = circuit_slice_insert arr_c (to_int i) bs_c in
            convert_output (`CArray (w, n)) (res_c :> circuit)
          | _ -> assert false
          end 
        | args -> 
          if debug then Format.eprintf "Bad arguments for array slice set:@.w=%d@.%a@." w
          (fun fmt args -> List.iter (Format.fprintf fmt "%a@\n" pp_arg) args) args;
          assert false
        end

      (* FIXME: what do we want for out of bounds extract? Decide later *)
      | { kind = `Extract (w_in, w_out) } -> 
        begin match args with
        | [ `Circuit ((`CBitstring _, _ ) as c) ; `Constant i ] ->
          circuit_slice ~size:w_out c (to_int i) 
        | _ -> assert false
        end
      | { kind = `Insert (w_orig, w_ins) } -> 
        begin match args with
        | [ `Circuit ((`CBitstring _, _) as orig_c) ; `Constant i ; `Circuit ((`CBitstring _, _) as new_c) ] ->
            (circuit_slice_insert orig_c (to_int i) new_c :> circuit)
        | _ -> assert false
        end

      | { kind = `Map (w_i, w_o, n) } -> 
        begin match args with 
        | [ `Circuit ((`CBitstring _, [{type_=`CBitstring w_i'}; _]) as cf); `Circuit (`CArray (arr, w_i''), arr_inps) ] when (w_i' = w_i && w_i'' = w_i') && (Backend.size_of_reg arr / w_i = n) ->
          let circs, inps = List.split @@ List.map (fun c -> 
            match circuit_compose cf [c] with
            | (`CBitstring res, inps) -> res, inps 
            | _ -> assert false
            ) 
          (List.init n (fun i -> `CBitstring (Backend.slice arr (i*w_i) w_i), []))
          in
          (assert (List.for_all ((=) (List.hd inps)) inps));
          let inps = List.hd inps in
          let circ = `CArray (Backend.flatten circs, w_o) in  
          (circ, inps) 
        | _ -> assert false
        end
      | { kind = `Get w_in } -> 
        begin match args with
        | [ `Circuit (`CBitstring bs, cinps); `Constant i ] ->
          `CBool (Backend.get bs (to_int i)), cinps
        | _ -> assert false
        end
      | { kind = `AInit (n, w_o) } -> 
        begin match args with
        | [ `Init init_f ] -> 
          let circs, cinps = List.split @@ List.init n init_f in
          let circs = List.map (function | `CBitstring r when Backend.size_of_reg r = w_o -> r | _ -> assert false) circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          (`CArray (Backend.flatten circs, w_o), cinps) 
        | _ -> assert false
        end
      | { kind = `Init w } -> 
        begin match args with 
        | [ `Init init_f ] ->
          let circs, cinps = List.split @@ List.init w init_f in
          let circs = List.map (function | `CBool b -> b | _ -> assert false) circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          (`CBitstring (Backend.reg_of_node_list circs), cinps)
        | _ -> assert false
        end
      | _ -> assert false


      let circuit_of_bvop (op: EcDecl.crb_bvoperator) : circuit = 
      match op with
      | { kind = `Add size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.add c1 c2 ), [inp1; inp2] 

      | { kind = `Sub size } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.sub c1 c2), [inp1; inp2] 

      | { kind = `Mul  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.mul c1 c2), [inp1; inp2] 

      | { kind = `Div (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.udiv c1 c2), [inp1; inp2] 

      | { kind = `Div (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.sdiv c1 c2), [inp1; inp2] 

      | { kind = `Rem (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.umod c1 c2), [inp1; inp2] 

      | { kind = `Rem (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.smod c1 c2), [inp1; inp2] 
        (* Should this be mod or rem? TODO FIXME*)

      | { kind = `Shl  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.lshl c1 c2), [inp1; inp2] 

      | { kind = `Shr  (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.lshr c1 c2), [inp1; inp2] 

      | { kind = `Shr  (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.ashr c1 c2), [inp1; inp2] 

      | { kind = `Rol  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.rol c1 c2), [inp1; inp2] 

      | { kind = `Ror  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.ror c1 c2), [inp1; inp2] 

      | { kind = `And  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.land_ c1 c2), [inp1; inp2] 

      | { kind = `Or   size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.lor_ c1 c2), [inp1; inp2] 

      | { kind = `Xor  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.lxor_ c1 c2), [inp1; inp2] 

      | { kind = `Not  size } -> 
        let c1, inp1 = new_cbitstring_inp_reg size in 
        `CBitstring (Backend.lnot_ c1), [inp1] 

      | { kind = `Lt (size, false) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBool (Backend.ult c1 c2), [inp1; inp2] 
      
      | { kind = `Lt (size, true) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBool (Backend.slt c1 c2), [inp1; inp2] 

      | { kind = `Le (size, false) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBool (Backend.ule c1 c2), [inp1; inp2] 

      | { kind = `Le (size, true) } ->
        let c1, inp1 = new_cbitstring_inp_reg size in 
        let c2, inp2 = new_cbitstring_inp_reg size in
        `CBool (Backend.sle c1 c2), [inp1; inp2] 

      | { kind = `Extend (size, out_size, false) } ->
        (* assert (size <= out_size); *)
        let c1, inp1 = new_cbitstring_inp_reg size in 
        `CBitstring (Backend.uext c1 out_size), [inp1] 

      | { kind = `Extend (size, out_size, true) } ->
        (* assert (size <= out_size); *)  
        let c1, inp1 = new_cbitstring_inp_reg size in 
        `CBitstring (Backend.sext c1 out_size), [inp1] 

      | { kind = `Truncate (size, out_sz) } ->
        (* assert (size >= out_sz); *)
        let c1, inp1 = new_cbitstring_inp_reg size in
        `CBitstring (Backend.trunc c1 out_sz), [inp1] 

      | { kind = `Concat (sz1, sz2, szo) } ->
        (* assert (sz1 + sz2 = szo); *)
        let c1, inp1 = new_cbitstring_inp_reg sz1 in 
        let c2, inp2 = new_cbitstring_inp_reg sz2 in
        `CBitstring (Backend.concat c1 c2), [inp1; inp2] 

      | { kind = `A2B ((w, n), m)} ->
        (* assert (n * w = m); *)
        let c1, inp1 = new_carray_inp w n |-> ((fun (`CArray (r, _)) -> r), idnt) in  
        `CBitstring c1, [inp1] 

      | { kind = `B2A (m, (w, n))} ->
        (* assert (n * w = m); *)
        let c1, inp1 = new_cbitstring_inp m |-> ((fun (`CBitstring r) -> r), idnt) in  
        `CArray (c1, w), [inp1] 

      | { kind = `ASliceGet _ | `ASliceSet _ | `Extract _ | `Insert _ | `Map _ | `AInit _ | `Get _ | `Init _  } -> assert false

      (* | _ -> raise @@ CircError "Failed to generate op"  *)
    end

    module ArrayOps = struct
      let array_get ((`CArray (r, w), inps): carray cfun) (i: int) : circuit = 
        try 
          `CBitstring (Backend.slice r (i*w) w), inps  
        with Invalid_argument _ ->
          assert false

      let array_set ((`CArray (r, w), inps) : carray cfun) (pos: int) ((`CBitstring bs, cinps): cbitstring cfun) : circuit =
        try
          assert (w = Backend.size_of_reg bs);
          `CArray (Backend.insert r (pos * w) bs, w),
          merge_inputs inps cinps
        with 
          Invalid_argument _ -> assert false 
        | Assert_failure e -> 
            if debug then Format.eprintf "Array set size mismatch arr[%d (bits)@%d (block size)], w@%d@." 
            (Backend.size_of_reg r) 
            w 
            (Backend.size_of_reg bs);
          raise (Assert_failure e)

    (* FIXME: review this functiono | FIXME: Not axiomatized in QFABV.ec file *)
      let array_oflist (circs : circuit list) (dfl: circuit) (len: int) : circuit =
        let circs, inps = List.split circs in
        let dif = len - List.length circs in
  (*       if debug then Format.eprintf "Len, Dif in array_oflist: %d, %d@." len dif; *)
        let circs = circs @ (List.init dif (fun _ -> fst dfl)) in
        let inps = if dif > 0 then inps @ [snd dfl] else inps in
        let circs = List.map 
          (function 
            | `CBitstring r -> r
            | _ -> assert false (* FIXME: error handling *)
          ) circs
        in
        `CArray (Backend.flatten circs, Backend.size_of_reg (List.hd circs)), merge_inputs_list inps 
    end
end

include MakeCircuitInterfaceFromCBackend(LospecsBack)
include PState
include LocalCache
include CArgs
include BVOps
include ArrayOps
