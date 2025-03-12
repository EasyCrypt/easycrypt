(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
open EcEnv
open EcAst
open EcCoreFol
open EcIdent
open LDecl

(* -------------------------------------------------------------------- *)
module Map = Batteries.Map
module Hashtbl = Batteries.Hashtbl
module Set = Batteries.Set
module Option = Batteries.Option

(* -------------------------------------------------------------------- *)
module C = struct
  include Lospecs.Aig
  include Lospecs.Circuit
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.Hlaig
end

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

let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({size=size_arr}, {size=size_bs}) -> size_arr * size_bs
  | _ -> match EcEnv.Circuit.lookup_bitstring_size env t with
    | Some w -> w
    | None -> let err = Format.asprintf "No bitvector binding for type %a@."
    (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in 
    raise (CircError err)
  
let destr_array_type (env: env) (t: ty) : (int * ty) option = 
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({size}, {type_}) -> Some (size, EcTypes.tconstr type_ [])
  | _ -> None

let shape_of_array_type (env: env) (t: ty) : (int * int) = 
    match t.ty_node with
    | Tconstr (p, [et]) -> 
      begin match EcEnv.Circuit.lookup_array_path env p with
      | Some {size; _} -> size, width_of_type env et
      | None -> 
        let err = Format.asprintf "Failed to lookup shape of array type %a@."
        (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in
        raise (CircError err)
      end
    | _ -> 
      let err = Format.asprintf "Failed to lookup shape of array type %a@."
      (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in
      raise (CircError err)

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

let circuit_from_spec_ (env: env) (p : path) : C.reg list -> C.reg  =
  (* | "OPP_8" -> C.opp (args |> registers_of_bargs env |> List.hd) (* FIXME: Needs to be in spec *) *)
  match EcEnv.Circuit.lookup_circuit_path env p with
  | Some circuit ->
    (fun regs -> C.circuit_of_specification regs circuit) 
  | None -> let err = Format.sprintf "No operator for path: %s@."
    (let a,b = EcPath.toqsymbol p in List.fold_right (fun a b -> a ^ "." ^ b) a b) in
    raise (CircError err)



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
  type cinp = {
    type_ : [`CIArray of (int * int) | `CIBitstring of int | `CITuple of int list | `CIBool ];
    id: int
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 
  
  module CArgs : sig
    type arg 

    val arg_of_circuit : circuit -> arg
    val arg_of_zint : zint -> arg
    val arg_of_circuits : circuit list -> arg
    val arg_of_init : (int -> circuit) -> arg
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
    val update_cache : cache -> lpattern -> circuit -> cache
    val cache_get : cache -> ident -> circuit
    val empty_cache : cache
    val cache_map : (ident -> circuit -> circuit) -> cache -> cache
  end

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
  val circuit_true : (cbool * (cinp list)) 
  val circuit_false : (cbool * (cinp list)) 

  (* <=> circuit has not inputs (every input is unbound) *)
  val circuit_is_free : circuit -> bool
  
  (* Direct circuuit constructions *)
  val circuit_ite : c:(cbool * (cinp list)) -> t:circuit -> f:circuit -> circuit
  val circuit_eq : circuit -> circuit -> cbool cfun

  (* Circuits from operators *)
  val op_is_base : env -> path -> bool 
  val op_is_parametric_base : env -> path -> bool
  val circuit_of_op : env -> path -> circuit (* Fails if circuit takes a constant arg *)
  val circuit_of_op_with_args : env -> path -> arg list -> circuit

  (* Circuit tuples *)
  val circuit_tuple_proj : (ctuple * (cinp list)) -> int -> (cbitstring * (cinp list)) 
  val circuit_tuple_of_circuits : (cbitstring * (cinp list)) list -> (ctuple * (cinp list))
  val circuits_of_circuit_tuple : (ctuple * (cinp list)) -> (cbitstring * (cinp list)) list

  (* Circuit lambdas, for managing inputs *)
  val open_circ_lambda : env -> (ident * ty) list -> circuit list 
  val open_circ_lambda_cache : env -> LocalCache.cache -> (ident * ty) list -> LocalCache.cache 
  val open_circ_lambda_pstate : env -> PState.pstate -> (ident * ty) list -> PState.pstate 
  val close_circ_lambda : env -> (ident * ty) list -> circuit -> circuit 
  val close_circ_lambda_cache : env -> LocalCache.cache -> (ident * ty) list -> LocalCache.cache 
  val close_circ_lambda_pstate : env -> PState.pstate -> (ident * ty) list -> PState.pstate 

  (* Avoid nodes for uninitialized inputs *)
  val circuit_uninit : env -> ty -> circuit
  val circuit_has_uninitialized : circuit -> bool

  (* Circuit equivalence call, should do some processing and then call some backend *)
  val circ_equiv : ?pcond:(cbool * (cinp list)) -> circuit -> circuit -> bool

  (* Composition of circuit functions, should deal with inputs and call some backend *)
  val circuit_compose : circuit -> circuit list -> circuit

  (* Computing the function given by a circuit *)
  val compute : sign:bool -> cbitstring cfun -> arg list -> zint

  (* Mapreduce/Dependecy analysis related functions *)
  val is_decomposable : int -> int -> cbitstring cfun -> bool
  val decompose : int -> int -> cbitstring cfun -> (cbitstring cfun) list 
  val permute : int -> (int -> int) -> cbitstring cfun -> cbitstring cfun

  (* Wraps the backend call to deal with args/inputs *)
  module CircuitSpec : sig
    val circuit_from_spec : env -> [`Path of path | `Bind of EcDecl.crb_circuit] -> circuit 
    val op_has_spec : env -> path -> bool
  end
end

(* Backend implementing minimal functions needed for the translation *)
(* Minimal expected functionality is QF_ABV *)
(* Input are: some identifier + some bit *)
module type CBackend = sig
  type node (* Corresponds to a single output node *)
  type reg
  (* Id + offset, both assumed starting at 0 *)
  type inp = int * int

  val true_ : node
  val false_ : node

  val bad : node
  val has_bad : node -> bool

  val node_array_of_reg : reg -> node array
  val node_list_of_reg : reg -> node list
  val reg_of_node_list : node list -> reg
  val reg_of_node_array : node array -> reg

  val input_node : id:int -> int -> node
  val input_of_size : ?offset:int -> id:int -> int -> reg

  val reg_of_zint : size:int -> zint -> reg
  val bool_array_of_reg : reg -> bool array
  val bool_list_of_reg : reg -> bool list
  val szint_of_reg : reg -> zint
  val uzint_of_reg : reg -> zint

  val apply : (inp -> node option) -> node -> node
  val circuit_from_spec : Lospecs.Ast.adef -> reg list -> reg 
  val equiv : ?inps:inp list -> pcond:node -> reg -> reg -> bool

  val node_eq : node -> node -> node
  val ite : node -> node -> node -> node

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
  end
end

module TestBack : CBackend = struct
  type node = C.node
  type reg = C.node array
  type inp = int * int

  let true_ = C.true_
  let false_ = C.false_
  let bad = C.input (-1, -1)
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
      | C.Input (-1, -1) -> false
      | C.Input _
      | C.False -> true
      | C.And (n1, n2) -> (doit n1) || (doit n2)
    in
    fun b -> doit b

  let node_array_of_reg : reg -> node array = fun x -> x
  let node_list_of_reg : reg -> node list = fun x -> Array.to_list x  
  let reg_of_node_list : node list -> reg = fun x -> Array.of_list x
  let reg_of_node_array : node array -> reg = fun x -> x

  let reg_of_zint ~(size: int) (v: zint) : reg = 
    Array.of_list (C.of_bigint_all ~size (BI.to_zt v))

  let bool_array_of_reg (r: reg) : bool array = 
    Array.map (fun r -> 
      match (r :> C.node) with 
      | { gate = False; id } when id > 0 -> false
      | { gate = False; id } when id < 0 -> true
      | _ -> assert false (* FIXME: Error handling *)
    ) r

  let bool_list_of_reg (r: reg) : bool list = 
    List.init (Array.length r) (fun i -> 
      match r.(i) with 
      | { gate = False; id } when id > 0 -> false
      | { gate = False; id } when id < 0 -> true
      | _ -> assert false (* FIXME: Error handling *)
    )

  let szint_of_reg (r: reg) : zint = 
    bool_list_of_reg r |> C.sbigint_of_bools |> BI.of_zt 

  let uzint_of_reg (r: reg) : zint = 
    bool_list_of_reg r |> C.ubigint_of_bools |> BI.of_zt
    
  let node_eq (n1: node) (n2: node) = C.xnor n1 n2
  let ite (c: node) (t: node) (f: node) = C.mux2 f t c 

  let equiv ?(inps: inp list option) ~(pcond: node) (r1: reg) (r2: reg) : bool = 
    let open HL in
    let module BWZ = (val makeBWZinterface ()) in
    BWZ.circ_equiv ?inps (node_list_of_reg r1) (node_list_of_reg r2) pcond  

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
        Array.for_all (fun (_, d) ->
          if Map.is_empty d then true
          else
          let _, bits = Map.any d in
          Set.is_empty bits ||
          let base = Set.at_rank_exn 0 bits in
          Set.for_all (fun bit ->
            let dist = bit - base in
            0 <= dist && dist < w_in
          ) bits
        ) blocks
      | _ -> 
        (Format.eprintf "Failed first check@\n"; 
        Format.eprintf "Map keys: ";
        Array.iteri (fun i dep ->
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
  end

end

(* Make this into a functor over some backend *)
module MakeCircuitInterfaceFromCBackend(Backend: CBackend) : CircuitInterface = struct
  (* Module Types *)
  type count = int
  type width = int
  type carray_type = Backend.node array * width 
  type cbitstring_type = Backend.node array
  type ctuple_type = Backend.node array * (width list)
  type cbool_type = Backend.node
  type carray = [`CArray of carray_type ]
  type cbool = [`CBool of cbool_type ]
  type cbitstring = [`CBitstring of cbitstring_type ]
  type ctuple = [`CTuple of ctuple_type ]
  type circ = [cbool | carray | cbitstring | ctuple]
  type cinp = {
    type_ : [`CIArray of (width * count) | `CIBitstring of width | `CITuple of width list | `CIBool];
    id : int;
  }
  type 'a cfun = 'a * (cinp list)
  type circuit = circ cfun 

  (* Helper functions *)
  let (|->) ((a,b)) ((f,g)) = (f a, g b)
  let idnt = fun x -> x

  (* Pretty printers *)
  let pp_cinp (fmt: Format.formatter) (inp: cinp) : unit = 
    Format.eprintf "Input(id: %d, type = %s)" inp.id 
    (match inp.type_ with
    | `CIArray (w, n)  -> Format.sprintf "Array(%d@%d)" n w 
    | `CIBool -> "Bool"
    | `CITuple _ -> "Tuple" 
    | `CIBitstring w -> Format.sprintf "Bitstring@%d" w )

  let pp_circ (fmt : Format.formatter) (c: circ) : unit =
    match c with
    | `CArray _ -> Format.eprintf "Circ(Array)"
    | `CBitstring _ -> Format.eprintf "Circ(Bitstring)"
    | `CTuple _ -> Format.eprintf "Circ(Tuple)"
    | `CBool _ -> Format.eprintf "Circ(Bool)"
    
  let pp_circuit (fmt: Format.formatter) ((c, inps) : circuit) : unit =
    Format.eprintf "@[<hov 2>%a: @\n%a@]@\n"
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
    cs @ ds

  let merge_inputs_list (cs: cinp list list) : cinp list =
    List.fold_right (merge_inputs) cs []

  let merge_circuit_inputs (c: circuit) (d: circuit) : cinp list =
    merge_inputs (snd c) (snd d)

  let unify_inputs_renamer (target: cinp list) (inps: cinp list) : Backend.inp -> cbool_type option =
    let map = List.fold_left2 (fun map inp1 inp2 -> match inp1, inp2 with
      | {type_ = `CIBitstring w ; id=id_tgt},
        {type_ = `CIBitstring w'; id=id_orig} when w = w' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init w (fun i -> i))
      | {type_ = `CIArray (w , n ); id=id_tgt},
        {type_ = `CIArray (w', n'); id=id_orig} when w = w' && n = n' -> 
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w*n) (fun i -> i))
      | {type_ = `CITuple szs ; id=id_tgt},
        {type_ = `CITuple szs'; id=id_orig} when szs = szs' -> 
          let w = List.sum szs in
          List.fold_left (fun map i -> Map.add (id_orig, i) (Backend.input_node ~id:id_tgt i) map) 
            map (List.init (w) (fun i -> i))
      | {type_ = `CIBool; id=id_tgt},
        {type_ = `CIBool; id=id_orig} ->
          Map.add (id_orig, 0) (Backend.input_node ~id:id_tgt 0) map
      | _ -> Format.eprintf "Mismatched inputs:@\nInp1: %a@\nInp2: %a@\n" pp_cinp inp1 pp_cinp inp2; assert false 
    ) Map.empty target inps in
    fun inp -> Map.find_opt inp map

  (* Renames circuit2 inputs to match circuit 1 *)
  let unify_inputs (target: cinp list) ((c2, inps2): 'a cfun) : 'a = 
    let map_ = unify_inputs_renamer target inps2 in
    let circ = match c2 with
    | `CBitstring r -> `CBitstring (Array.map (Backend.apply map_) r)
    | `CArray (r,w) -> `CArray (Array.map (Backend.apply map_) r, w)
    | `CTuple (r, szs) -> `CTuple (Array.map (Backend.apply map_) r, szs)
    | `CBool b -> `CBool (Backend.apply map_ b)
    in
    circ 

  let circuit_input_compatible ?(strict = false) ((c, _): circuit) (cinp: cinp) : bool =
    match c, cinp with
    | `CBitstring r, { type_ = `CIBitstring w } when Array.length r = w -> true
    | `CArray (r, w), { type_ = `CIArray (w', n)} when Array.length r = w'*n && w = w' -> true
    | `CTuple (r, szs), { type_ = `CITuple szs' } when szs = szs' -> true
    | `CBool _, { type_ = `CIBool } -> true
    | `CBool _, { type_ = `CIBitstring 1 } when not strict -> true
    | `CBitstring r, { type_ = `CIBool } when not strict && Array.length r = 1 -> true
    | _ -> false

  (* Type conversions *)
  let reg_of_circ (c: circ) : Backend.reg = 
    match c with
    | `CTuple (r, _) | `CArray (r, _) 
    | `CBitstring r -> Backend.reg_of_node_array r
    | `CBool r -> Backend.reg_of_node_array [| r |] 

  let cbool_of_circuit ?(strict : bool = false) (c: circuit) : (cbool * (cinp list)) = 
    match (fst c) with
    | `CArray (r, _) | `CTuple (r, _) | `CBitstring r 
      when (not strict) && Array.length r = 1 
        -> `CBool (r.(0)), snd c
    | `CBool _ as r -> (r, snd c) 
    | _ -> assert false

  let cbitstring_of_circuit ?(strict : bool = false) (c: circuit) : (cbitstring * (cinp list)) =
    match (fst c) with
    | `CArray (r, _) | `CTuple (r, _) 
      when not strict -> `CBitstring r, snd c
    | `CBitstring _ as r -> (r, snd c)
    | `CBool r -> (`CBitstring [| r |], snd c)
    | _ -> assert false

  (* FIXME: is this a good convetion? *)
  let carray_of_circuit ?(strict : bool = false) (c: circuit) : (carray * (cinp list)) =
    match (fst c) with
    | `CArray _ as r -> r, snd c
    | `CTuple (r, _ ) | `CBitstring r 
      when not strict -> `CArray (r, Array.length r), snd c
    | `CBool r when not strict -> `CArray ([| r |], 1), snd c
    | _ -> assert false

  let ctuple_of_circuit ?(strict : bool = false) (c: circuit) : (ctuple * (cinp list)) =
    match (fst c) with
    | `CArray (r, _) | `CBitstring r 
      when not strict -> `CTuple (r, [ Array.length r ]), snd c
    | `CTuple _ as r -> r, snd c
    | `CBool r when not strict -> `CTuple ([| r |], [ 1 ]), snd c
    | _ -> assert false

  (* Circuit tuples *)
  let circuit_tuple_proj ((`CTuple (r, ws)), inps: ctuple * (cinp list)) (i: int) =
    let idx, w = List.takedrop i ws in
    let w = List.hd w in
    let idx = List.fold_left (+) 0 idx in
    `CBitstring (Array.sub r idx w), inps

  let circuit_tuple_of_circuits (cs: (cbitstring * (cinp list)) list) : ctuple * (cinp list) = 
    let circ, lens = List.fold_left_map (fun acc (`CBitstring r) -> (Array.to_list r) @ acc, Array.length r) [] (List.fst cs) in 
    let circ = Array.of_list (List.rev circ) in
    let inps = List.snd cs in
    `CTuple (circ, lens) , merge_inputs_list inps

  let circuits_of_circuit_tuple ((`CTuple (tp, szs), tpinps) : (ctuple * cinp list)) : (cbitstring * cinp list) list = 
    snd @@ List.fold_left_map 
      (fun idx sz -> 
        (idx + sz, 
        (`CBitstring (Array.sub tp idx sz), tpinps)))
      0 szs 
  
  (* CACHE DEFINIITION *)
  (*type cache  = (ident, (cinput * circuit)) Map.t*)
  module LocalCache = struct
    type cache = (ident, circuit) Map.t
    let update_cache (cache: cache) (lp: lpattern) (c: circuit) : cache = 
      match lp, c with
      | LTuple vs, (`CTuple r1 as tp, inps) -> 
          let comps = circuits_of_circuit_tuple (tp, inps) in
          assert (List.compare_lengths vs comps = 0);
          List.fold_left2 (fun cache (v, _t) c -> 
            Map.add v c cache
          )
          cache vs (comps :> circuit list)
      | LTuple _, _ | LRecord _, _ -> assert false
      | LSymbol (idn, t), c -> Map.add idn c cache

    let cache_get (cache: cache) (idn: ident) : circuit = 
      try 
        Map.find idn cache  
      with Not_found -> 
        assert false (* FIXME: Error handling *)

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
    `CBool inp, { type_ = `CIBool; id; }

  let new_cbitstring_inp ?(name = `Str "input") (sz: int) : cbitstring * cinp =
    let id, r = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.(node_array_of_reg @@ input_of_size ~id sz )
    | `Idn idn -> let id = tag idn in
      id, Backend.(node_array_of_reg @@ input_of_size ~id sz )
    | `Bad -> 
      -1, Array.make sz Backend.bad   
    in
    `CBitstring r, 
    { type_ = `CIBitstring sz; id; }

  let new_carray_inp ?(name = `Str "input") (el_sz: int) (arr_sz: int) : carray * cinp = 
    let id, arr = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
      id, Backend.(node_array_of_reg @@ input_of_size ~id (el_sz * arr_sz)) 
    | `Idn idn -> let id = tag idn in
      id, Backend.(node_array_of_reg @@ input_of_size ~id (el_sz * arr_sz)) 
    | `Bad -> 
      -1, Array.make (el_sz * arr_sz) Backend.bad
    in
    `CArray (arr, el_sz), 
    { type_ = `CIArray (el_sz, arr_sz); id; } 

  let new_ctuple_inp ?(name = `Str "input") (szs: int list) : ctuple * cinp =
    let id, tp = match name with 
    | `Str name -> let id = EcIdent.create name |> tag in
    id, Backend.(node_array_of_reg @@ input_of_size ~id (List.sum szs))
    | `Idn idn -> let id = tag idn in
    id, Backend.(node_array_of_reg @@ input_of_size ~id (List.sum szs))
    | `Bad ->
      -1, Array.make (List.sum szs) Backend.bad
    in
    `CTuple (tp, szs),
    { type_ = `CITuple szs;
      id; }

  let circuit_true  = `CBool Backend.true_ , [] 
  let circuit_false = `CBool Backend.false_, []
  let circuit_is_free (f: circuit) : bool = List.is_empty @@ snd f 

  let circuit_ite ~(c: cbool * (cinp list)) ~(t: circuit) ~(f: circuit) : circuit =
    assert ((circuit_is_free t) && (circuit_is_free f) && (circuit_is_free (c :> circuit)));
    let (`CBool c) = (fst c) in
    match (fst t, fst f) with
    | `CBitstring rt, `CBitstring rf -> (`CBitstring (Array.map2 (Backend.ite c)  rt rf), [])   
    | `CArray (rt, wt), `CArray (rf, wf) when wt = wf -> (`CArray (Array.map2 (Backend.ite c) rt rf, wt), []) 
    | `CTuple (rt, szs_t), `CTuple (rf, szs_f) when szs_t = szs_f -> (`CTuple (Array.map2 (Backend.ite c) rt rf, szs_t), []) 
    | `CBool t, `CBool f -> (`CBool (Backend.ite c t f) , [])
    | _ -> assert false

  let circuit_eq (c: circuit) (d: circuit) : (cbool cfun) =  
    match c, d with
    | (`CArray (r1, _), inps1), (`CArray (r2, _), inps2) 
    | (`CTuple (r1, _), inps1), (`CTuple (r2, _), inps2) 
    | (`CBitstring r1, inps1), (`CBitstring r2, inps2) ->
        `CBool (Array.fold (Backend.band) Backend.true_ (Array.map2 (fun c d -> Backend.node_eq c d) r1 r2)), merge_inputs inps1 inps2 
    | _ -> assert false
    
  let circuit_compose (c: circuit) (args: circuit list) : circuit = 
    (try
      assert (List.for_all2 (fun c cinp -> circuit_input_compatible c cinp) args (snd c))
    with 
      Assert_failure _ -> 
        Format.eprintf "Error on application:@\nTarget:%a@\n@[<hov 2>Args:%a@]@\n"
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
            Some (r.(idx))
          with Invalid_argument _ -> None 
          end
        | `CBool b when idx = 0 -> Some b
        | _ -> None
      ) 
    in
    let circ = match (fst c) with
    | `CBool b -> `CBool (Backend.apply map_ b)
    | `CArray (r, w) -> `CArray (Array.map (Backend.apply map_) r, w)
    | `CBitstring r -> `CBitstring (Array.map (Backend.apply map_) r)
    | `CTuple (r, szs) -> `CTuple (Array.map (Backend.apply map_) r, szs)
    in
    let inps = merge_inputs_list (List.snd args) in
    (circ, inps)

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
      | `Path p -> let op = match EcEnv.Circuit.lookup_bvoperator_path env p with
        | Some op -> op
        | None -> assert false
        in op
      in
      match op with 
      | { kind = `ASliceGet ((w, n), m) } -> 
        begin match args with 
        | [ `Circuit (`CArray (r, w'), cinps) ; `Constant i ] when w = w' ->
            (`CBitstring (Array.sub r (BI.to_int i) m), cinps)
        | _ -> assert false
        end
      | { kind = `ASliceSet ((w, n), m) } -> 
          begin match args with 
          | [ `Circuit (`CArray (arr, w'), arrinps) ; `Circuit (`CBitstring bs, bsinps) ; `Constant i ] when w = w' ->
            let i = BI.to_int i in
            ((`CArray 
              (Array.init (w*n) (fun j -> 
                if 0 <= j-i && j-i < m then 
                  bs.(j-i)
                else
                  arr.(j)), 
              w)), 
            merge_inputs arrinps bsinps) 
          | _ -> assert false
          end
      (* FIXME: what do we want for out of bounds extract? Decide later *)
      | { kind = `Extract (w_in, w_out) } -> 
        begin match args with
        | [ `Circuit (`CBitstring r, cinps) ; `Constant i ] ->
            (`CBitstring (Array.sub r (BI.to_int i) w_out), cinps) 
        | _ -> assert false
        end
      | { kind = `Insert (w_orig, w_ins) } -> 
        begin match args with
        | [ `Circuit (`CBitstring origbs, cinps) ; `Constant i ; `Circuit (`CBitstring newbs, cinps2) ] ->
            let resbs = Array.copy origbs in 
            (Array.blit newbs 0 (Array.copy origbs) (BI.to_int i) w_ins);
            (`CBitstring resbs, merge_inputs cinps cinps2)
        | _ -> assert false
        end

      | { kind = `Map (w_i, w_o, n) } -> 
        begin match args with 
        | [ `Circuit ((`CBitstring _, [{type_=`CIBitstring w_i'}; _]) as cf); `Circuit (`CArray (arr, w_i''), arr_inps) ] when (w_i' = w_i && w_i'' = w_i') && (Array.length arr / w_i = n) ->
          let circs, inps = List.split @@ List.map (fun c -> 
            match circuit_compose cf [c] with
            | (`CBitstring res, inps) -> res, inps 
            | _ -> assert false
            ) 
          (List.init n (fun i -> `CBitstring (Array.sub arr (i*w_i) w_i), []))
          in
          (assert (List.for_all ((=) (List.hd inps)) inps));
          let inps = List.hd inps in
          let circ = `CArray (Array.concat circs, w_o) in  
          (circ, inps) 
        | _ -> assert false
        end
      | { kind = `Get w_in } -> 
        begin match args with
        | [ `Circuit (`CBitstring bs, cinps); `Constant i ] ->
          `CBool (bs.(BI.to_int i)), cinps
        | _ -> assert false
        end
      | { kind = `AInit (n, w_o) } -> 
        begin match args with
        | [ `Init init_f ] -> 
          let circs, cinps = List.split @@ List.init n init_f in
          let circs = List.map (function | `CBitstring r when Array.length r = w_o -> r | _ -> assert false) circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          (`CArray (Array.concat circs, w_o), cinps) 
        | _ -> assert false
        end
      | { kind = `Init w } -> 
        begin match args with 
        | [ `Init init_f ] ->
          let circs, cinps = List.split @@ List.init w init_f in
          let circs = List.map (function | `CBool b -> b | _ -> assert false) circs in
          (assert (List.for_all ((=) (List.hd cinps)) cinps));
          let cinps = List.hd cinps in
          (`CBitstring (Array.of_list circs), cinps)
        | _ -> assert false
        end
      | _ -> assert false

    let op_is_bvop (env: env) (op : path) : bool =
      match EcEnv.Circuit.lookup_bvoperator_path env op with
      | Some { kind = `Add _ }      | Some { kind = `Sub _ } 
      | Some { kind = `Mul _ }      | Some { kind = `Div _ }  
      | Some { kind = `Rem _ }      | Some { kind = `Shl _ }  
      | Some { kind = `Shr _ }      | Some { kind = `Rol _ }  
      | Some { kind = `Ror _ }      | Some { kind = `And _ }  
      | Some { kind = `Or _ }       | Some { kind = `Xor _ }  
      | Some { kind = `Not _ }      | Some { kind = `Lt _ } 
      | Some { kind = `Le _ }       | Some { kind = `Extend _ } 
      | Some { kind = `Truncate _ } | Some { kind = `Concat _ } 
      | Some { kind = `A2B _ }      | Some { kind = `B2A _ } -> true
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
      | `Path p -> let op = match EcEnv.Circuit.lookup_bvoperator_path env p with
        | Some op -> op
        | None -> assert false
        in op
      in
      match op with
      | { kind = `Add size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.add c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Sub size } ->
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.sub c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Mul  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.mul c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Div (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.udiv c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Div (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.sdiv c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Rem (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.umod c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Rem (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.smod c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 
        (* Should this be mod or rem? TODO FIXME*)

      | { kind = `Shl  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.lshl c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Shr  (size, false) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.lshr c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Shr  (size, true) } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.ashr c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Rol  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.rol c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Ror  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.ror c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `And  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.land_ c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Or   size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.lor_ c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Xor  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.lxor_ c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

      | { kind = `Not  size } -> 
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.lnot_ c1 |> Backend.node_array_of_reg), [inp1] 

      | { kind = `Lt (size, false) } ->
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBool (Backend.ult c1 c2), [inp1; inp2] 
      
      | { kind = `Lt (size, true) } ->
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBool (Backend.slt c1 c2), [inp1; inp2] 

      | { kind = `Le (size, false) } ->
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBool (Backend.ule c1 c2), [inp1; inp2] 

      | { kind = `Le (size, true) } ->
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBool (Backend.sle c1 c2), [inp1; inp2] 

      | { kind = `Extend (size, out_size, false) } ->
        (* assert (size <= out_size); *)
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.uext c1 out_size |> Backend.node_array_of_reg), [inp1] 

      | { kind = `Extend (size, out_size, true) } ->
        (* assert (size <= out_size); *)  
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.sext c1 out_size |> Backend.node_array_of_reg), [inp1] 

      | { kind = `Truncate (size, out_sz) } ->
        (* assert (size >= out_sz); *)
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.trunc c1 out_sz |> Backend.node_array_of_reg), [inp1] 

      | { kind = `Concat (sz1, sz2, szo) } ->
        (* assert (sz1 + sz2 = szo); *)
        let c1, inp1 = new_cbitstring_inp sz1 |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        let c2, inp2 = new_cbitstring_inp sz2 |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in 
        `CBitstring (Backend.concat c1 c2 |> Backend.node_array_of_reg), [inp1; inp2] 

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
  open BVOps

  module BitstringOps = struct
    type binding = crb_bitstring_operator 

    let bs_of_int (size: width) (v: zint) : circuit = 
      `CBitstring (Backend.node_array_of_reg @@
        Backend.reg_of_zint ~size v), []

    let op_is_bsop (env: env) (op: path) : bool = 
      match EcEnv.Circuit.reverse_bitstring_operator env op with
      | Some (_, `OfInt) -> true 
      | _ -> false

    let circuit_of_bsop (env: env) (op: [`Path of path | `BSBinding of binding]) (args: arg list) : circuit =
      let bnd = match op with
      | `BSBinding bnd -> bnd
      | `Path p -> begin match EcEnv.Circuit.reverse_bitstring_operator env p with
        | Some bnd -> bnd
        | None -> assert false
        end
      in
      match bnd with
      | bs, `From -> assert false (* doesn't translate to circuit *)
      | {size}, `OfInt -> begin match args with
        | [ `Constant i ] ->
          bs_of_int size i
        | _ -> assert false
      end
      | bs, `To -> assert false (* doesn't translate to circuit *)
      | bs, `ToSInt -> assert false (* doesn't translate to circuit *) 
      | bs, `ToUInt -> assert false (* doesn't translate to circuit *)
  end
  open BitstringOps

  module ArrayOps = struct
    type binding = crb_array_operator 

    let array_get ((`CArray (r, w), inps): carray cfun) (i: int) : circuit = 
      try 
        `CBitstring (Array.sub r (i*w) w), inps  
      with Invalid_argument _ ->
        assert false

    let array_set ((`CArray (r, w), inps) : carray cfun) (pos: int) ((`CBitstring bs, cinps): cbitstring cfun) : circuit =
      try
        let i = pos * w in 
        `CArray (Array.init (Array.length r)
          (fun idx -> 
            if (idx >= i && idx < i + w) 
              then bs.(idx - i)
              else r.(idx)), w),
        merge_inputs inps cinps
      with Invalid_argument _ -> assert false 

    (* FIXME: review this functiono | FIXME: Not axiomatized in QFABV.ec file *)
    let array_oflist (circs : circuit list) (dfl: circuit) (len: int) : circuit =
      let circs, inps = List.split circs in
      let dif = len - List.length circs in
      let circs = circs @ (List.init dif (fun _ -> fst dfl)) in
      let inps = if dif > 0 then inps @ [snd dfl] else inps in
      let circs = List.map 
        (function 
          | `CBitstring r -> r
          | _ -> assert false (* FIXME: error handling *)
        ) circs
      in
      `CArray (Array.concat circs, Array.length (List.hd circs)), merge_inputs_list inps 

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
        | None -> assert false
        end
      in
      match op with
      | (arr, `ToList) -> assert false (* We do not translate this to circuit *)
      | (arr, `Get) -> begin match args with
        | [ `Circuit ((`CArray _, inps) as arr); `Constant i] ->
          array_get arr (BI.to_int i)
        | _ -> assert false
      end
      (* FIXME: Check argument order *)
      | ({size}, `OfList) -> begin match args with 
        | [ `Circuit dfl; `List cs ] -> array_oflist cs dfl size
        | _ -> assert false
        end
      | (arr, `Set) -> begin match args with
        | [ `Circuit ((`CArray _, _) as arr); 
            `Constant i; 
            `Circuit ((`CBitstring _, _) as bs) ] ->
          array_set arr (BI.to_int i) bs
        | _ -> assert false
      end
  end
  open ArrayOps
 
  (* Circuit Lambda functions *)

  (* FIXME: Maybe make this convert things that are typed as bool into tbool? *)
  let circ_lambda_one (env:env) (idn: ident) (t: ty) : cinp * circuit = 
    match t.ty_node with
    | Ttuple ts -> let szs = List.map (width_of_type env) ts in
      let ctp, cinp = new_ctuple_inp ~name:(`Idn idn) szs in
      cinp, ((ctp, []) :> circuit)
    | Tconstr (_, _) -> begin match EcEnv.Circuit.lookup_array_and_bitstring env t with
      | None -> begin try 
        let bs_info = Option.get (EcEnv.Circuit.lookup_bitstring env t) in
        let cbs, cinp = new_cbitstring_inp ~name:(`Idn idn) bs_info.size in
        cinp, ((cbs, []) :> circuit)
      with Invalid_argument _ -> assert false 
      end
      | Some ({size=arr_sz}, {size=el_sz}) ->
          let ca, cinp = new_carray_inp ~name:(`Idn idn) el_sz arr_sz in
          cinp, ((ca, []) :> circuit)
    end
    | Tfun (_, _) -> assert false
    | Tglob _ -> assert false
    | Tunivar _ -> assert false
    | Tvar _ -> assert false

  let open_circ_lambda (env : env) (vs: (ident * ty) list) : circuit list = 
    List.map (fun (idn, t) -> snd @@ circ_lambda_one env idn t) vs 
    
  let open_circ_lambda_cache (env : env) (cache : cache) (vs : (ident * ty) list) : cache = 
    List.fold_left (fun cache ((idn, t) as v) -> 
      update_cache cache (LSymbol v) @@ snd @@ circ_lambda_one env idn t)
    cache vs 
    
  let open_circ_lambda_pstate (env : env) (pstate : pstate) (vs: (ident * ty) list) : pstate = 
    List.fold_left (fun pstate (idn, t) ->
      update_pstate pstate (name idn) @@ snd @@ circ_lambda_one env idn t)
    pstate vs

  let close_circ_lambda (env : env) (vs : (ident * ty) list) (c: circuit) : circuit = 
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one env idn t) vs) in
    (fst c, merge_inputs cinps (snd c))

  let close_circ_lambda_cache (env : env) (cache : cache) (vs: (ident * ty) list) : cache = 
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one env idn t) vs) in
    cache_map (fun _ c -> (fst c, merge_inputs cinps (snd c))) cache 

  let close_circ_lambda_pstate (env : env) (pstate : pstate) (vs: (ident * ty) list) : pstate =  
    let cinps = List.fst @@ (List.map (fun (idn, t) -> circ_lambda_one env idn t) vs) in
    map_pstate (fun _ c -> (fst c, merge_inputs cinps (snd c))) pstate

  (* Functions for dealing with uninitialized inputs *)
  let circuit_uninit (env:env) (t: ty) : circuit = 
    match t.ty_node with
    | Ttuple ts -> let szs = List.map (width_of_type env) ts in
      let ctp, cinp = new_ctuple_inp ~name:`Bad szs in
      ((ctp, []) :> circuit)
    | Tconstr (_, _) -> begin match EcEnv.Circuit.lookup_array_and_bitstring env t with
      | None -> begin try 
        let bs_info = Option.get (EcEnv.Circuit.lookup_bitstring env t) in
        let cbs, cinp = new_cbitstring_inp ~name:`Bad bs_info.size in
        ((cbs, []) :> circuit)
      with Invalid_argument _ -> assert false 
      end
      | Some ({size=arr_sz}, {size=el_sz}) ->
          let ca, cinp = new_carray_inp ~name:`Bad el_sz arr_sz in
          ((ca, []) :> circuit)
    end
    | Tfun (_, _) -> assert false
    | Tglob _ -> assert false
    | Tunivar _ -> assert false
    | Tvar _ -> assert false

  let circuit_has_uninitialized (c: circuit) : bool =
    match (fst c) with
    | `CBitstring r | `CArray (r, _) | `CTuple (r, _) ->
        not @@ Array.for_all (fun b -> not @@ Backend.has_bad b) r
    | `CBool b -> 
      Backend.has_bad b

  let circ_equiv ?(pcond:(cbool * cinp list) option) ((c1, inps1): circuit) ((c2, inps2): circuit) : bool = 
    let () = Format.eprintf "c1: %a@\nc2: %a@\n" pp_circuit  (c1, inps1) pp_circuit (c2, inps2) in
    let pcc = match pcond with
    | Some (`CBool b, pcinps) -> 
        Backend.apply (unify_inputs_renamer inps1 pcinps) b
    | None -> Backend.true_ 
    in
    (* TODO: add code to check that inputs match *)
    let c2 = unify_inputs inps1 (c2, inps2) in
    let inps = List.map (function 
      | { type_ = `CIBool; id } -> (id, 1)
      | { type_ = `CIBitstring w; id } -> (id, w) 
      | { type_ = `CIArray (w1, w2); id } -> (id, w1*w2)
      | { type_ = `CITuple szs; id } -> (id, List.sum szs) 

    ) inps1 in
    match c1, c2 with
    | `CBitstring r1, `CBitstring r2 -> 
        Backend.equiv ~inps ~pcond:pcc (Backend.reg_of_node_array r1) (Backend.reg_of_node_array r2)
    | `CArray (r1, w1), `CArray (r2, w2) when w1 = w2 ->
        Backend.equiv ~inps ~pcond:pcc (Backend.reg_of_node_array r1) (Backend.reg_of_node_array r2)
    | `CTuple (r1, szs1), `CTuple (r2, szs2) when szs1 = szs2 ->
        Backend.equiv ~inps ~pcond:pcc (Backend.reg_of_node_array r1) (Backend.reg_of_node_array r2)
    | `CBool b1, `CBool b2 ->
        Backend.equiv ~inps ~pcond:pcc (Backend.reg_of_node_list [b1]) (Backend.reg_of_node_list [b2])
    | _ -> false
    

  module CircuitSpec = struct
    let circuit_from_spec env (c : [`Path of path | `Bind of EcDecl.crb_circuit ] ) = 
      let c = match c with
      | `Path p -> let c = EcEnv.Circuit.reverse_circuit env p in
        if (Option.is_some c) then Option.get c else assert false
      | `Bind c -> c
      in
      let _, temp_name = (EcPath.toqsymbol c.operator) in
      let temp_name = temp_name ^ "_spec_input" in
      let circ = Backend.circuit_from_spec c.circuit in
      let op = EcEnv.Op.by_path c.operator env in

      let rec unroll_fty_rev (acc: ty list) (ty: ty) : ty list =
        try 
          let a, b = EcTypes.tfrom_tfun2 ty in
          (unroll_fty_rev (a::acc) b)
        with
        | Assert_failure _ -> ty::acc
      in

      let argtys = unroll_fty_rev [] op.op_ty |> List.tl |> List.rev in
      let cinps, inps = List.map (fun ty -> 
        let id = EcIdent.create temp_name |> tag in
        let size : int = width_of_type env ty in
        (Backend.input_of_size ~id size, { type_ = `CIBitstring size; id = id; } )
        ) argtys |> List.split in
      let circ = circ cinps in
      `CBitstring (Backend.node_array_of_reg circ), inps

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
      assert false

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
      assert false

  (* Dependency analysis related functions. These assume one input/output and all bitstring types *)
  (* For more complex circuits, we might be able to simulate this with a int -> (int, int) map *)
  let is_decomposable (in_w: width) (out_w: width) ((`CBitstring r, inps) as c: cbitstring cfun) : bool = 
    match inps with
    | {type_=`CIBitstring w} :: [] when w mod in_w = 0 && Array.length r mod out_w = 0 ->
      let deps = Backend.Deps.deps_of_reg (Backend.reg_of_node_array r) in
      Backend.Deps.is_splittable in_w out_w deps 
    | _ -> 
        Format.eprintf "Failed decomposition type check@\n";
        Format.eprintf "In_w: %d | Out_w : %d | Circ: %a" in_w out_w pp_circuit c;
        false

  let split_renamer (n: count) (in_w: width) (inp: cinp) : (cinp array) * (Backend.inp -> cbool_type option) =
    match inp with
    | {type_ = `CIBitstring w; id} when w mod in_w = 0 ->
        let ids = Array.init n (fun i -> create ("split_" ^ (string_of_int i)) |> tag) in
        Array.map (fun id -> {type_ = `CIBitstring in_w; id}) ids, 
        (fun (id_, w) -> 
          if id <> id_ then None else
          let id_idx, bit_idx = (w / in_w), (w mod in_w) in
          Some (Backend.input_node ~id:ids.(id_idx) bit_idx))
    | _ -> assert false

  let decompose (in_w: width) (out_w: width) ((`CBitstring r, inps) as c: cbitstring cfun) : cbitstring cfun list = 
    if not (is_decomposable in_w out_w c) then 
      let deps = Backend.Deps.block_deps_of_reg out_w (Backend.reg_of_node_array r) in
      Format.eprintf "Failed to decompose. Deps:@.%a" (Backend.Deps.pp_block_deps) deps;
      assert false 
    else
    let n = (Array.length r) / out_w in
    let blocks = Array.init n (fun i -> 
      Array.sub r (i*out_w) out_w) in
    let cinps, renamer = split_renamer n in_w (List.hd inps) in
    Array.map2 (fun r inp ->
      let r = Array.map (Backend.apply renamer) r in
      (`CBitstring r, [inp])
    ) blocks cinps |> Array.to_list

  let permute (w: width) (perm: (int -> int)) ((`CBitstring r, inps): cbitstring cfun) : cbitstring cfun =
    let r = Array.init (Array.length r) (fun i ->
      let block_idx, bit_idx = (i / w), (i mod w) in
      let idx = (perm block_idx)*w + bit_idx in
      r.(idx)
    ) in
    `CBitstring r, inps

  let compute ~(sign: bool) ((`CBitstring r, inps) as c: cbitstring cfun) (args: arg list) : zint = 
    if List.compare_lengths args inps <> 0 then assert false else
    let args = List.map2 (fun arg inp ->
    match arg, inp with
    | `Circuit c, inp when circuit_input_compatible c inp -> c
    | `Constant i, {type_ = `CIBitstring size} -> `CBitstring (Backend.(node_array_of_reg @@ reg_of_zint ~size i)), []
    | _ -> assert false
    ) args inps 
    in
    match circuit_compose c args with
    | `CBitstring r, [] -> 
      let reg = Backend.reg_of_node_array r in
      if sign 
        then Backend.szint_of_reg reg
        else Backend.uzint_of_reg reg
    | _ -> assert false

  let circuit_of_op (env: env) (p: path) : circuit = 
    let op = try
      EcEnv.Circuit.reverse_operator env p |> List.hd
    with Failure _ -> 
      assert false
    in
    match op with
    | `Bitstring (bs, op) -> assert false 
    | `Array _ -> assert false 
    | `BvOperator bvbnd -> circuit_of_bvop  env (`BvBind bvbnd)
    | `Circuit c -> circuit_from_spec env (`Bind c)
    
  let circuit_of_op_with_args (env: env) (p: path) (args: arg list) : circuit  = 
    let op = try
      EcEnv.Circuit.reverse_operator env p |> List.hd
    with Failure _ -> 
      assert false
    in
    match op with
    | `Bitstring bsbnd -> circuit_of_bsop env (`BSBinding bsbnd) args
    | `Array abnd -> circuit_of_arrayop env (`ABinding abnd) args 
    | `BvOperator bvbnd -> circuit_of_parametric_bvop env (`BvBind bvbnd) args 
    | `Circuit c -> assert false (* TODO: Do we want to have parametric operators coming from the spec? Yes *) 

  let circuit_aggregate (cs: circuit list) : circuit =
    let inps = List.snd cs in
    let cs = List.map (fun c -> match cbitstring_of_circuit ~strict:false c with
    | `CBitstring r, _ -> r) cs in
    let c = Array.concat cs in
    let inps = merge_inputs_list inps in
    (`CBitstring c, inps)

  let input_aggregate_renamer (inps: cinp list) : cinp * (Backend.inp -> cbool_type option) =
    let new_id = create "aggregated" |> tag in
    let (size, map) = List.fold_left (fun (size, map) inp ->
      match inp with
      | { type_ = `CIBitstring w; id} ->
        (size + w, Map.add id (size, w) map) 
      | { type_ = `CIArray (w, n); id} ->
        (size + (w*n), Map.add id (size, w*n) map)
      | _ -> assert false
      ) (0, Map.empty) inps
    in
    {type_ = `CIBitstring size; id=new_id},
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
    | `CBitstring r -> `CBitstring (Array.map (Backend.apply renamer) r), [inp]
    | `CArray (r, w) -> `CArray (Array.map (Backend.apply renamer) r, w), [inp]
    | `CTuple (r, szs) -> `CTuple (Array.map (Backend.apply renamer) r, szs), [inp]
    | `CBool b -> `CBool (Backend.apply renamer b), [inp]


end

module ExampleInterface = MakeCircuitInterfaceFromCBackend(TestBack)
open ExampleInterface
open PState
open LocalCache
open CArgs
(* FIXME: why are all these openings required? *)

(* FIXME: move this to module? *)
let type_is_registered (env: env) (t: ty) : bool = 
  (Option.is_some (EcEnv.Circuit.lookup_array_and_bitstring env t)) ||
  (Option.is_some (EcEnv.Circuit.lookup_bitstring env t))


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
      Option.may (fun ppenv -> Format.eprintf "Failed to destructure claimed list: %a@." (EcPrinting.pp_form ppenv) f) ppenv;
      assert false

let (op_cache : circuit Mp.t ref) = ref Mp.empty

let circuit_of_form 
  ?(pstate  : pstate = empty_pstate) (* Program variable values *)
   (hyps    : hyps) 
   (f_      : EcAst.form) 
  : circuit =
  let cache = empty_cache in

  let rec doit (cache: cache) (hyps: hyps) (f_: form) : hyps * circuit = 
    let env = toenv hyps in
    let redmode = circ_red hyps in
    (* let redmode = {redmode with delta_p = fun _ -> `No} in *)
    let fapply_safe f fs = 
      let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
      res
    in

    let int_of_form ?(simplify = true) (f: form) : zint = 
      let f = 
        if simplify 
        then EcCallbyValue.norm_cbv redmode hyps f 
        else f
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
    in

    (* Supposed to be called on an apply *)
    let propagate_integer_arguments (op: form) (args: form list) : form =
      let op = 
        let pth, _ = destr_op op in
        match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
          f
        | _ -> 
          Format.eprintf "Failed to get body for op: %a\n" 
          (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) op;
          assert false
      in
      Format.eprintf "Propagating arguments for op: %a@\n" 
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) op;
      let res = fapply_safe op args in 
      Format.eprintf "Result: %a" 
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) res;
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
            doit cache hyps f) hyps (form_list_of_form ~ppenv:(EcPrinting.PPEnv.ofenv (LDecl.toenv hyps)) f) 
          in
          hyps, arg_of_circuits cs
      | _ -> assert false
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
      match Mp.find_opt pth !op_cache with
      | Some op -> 
        hyps, op
      | None -> 
      if op_is_base env pth then
        let circ = circuit_of_op env pth in
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ 
      else
        let hyps, circ = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
          doit cache hyps f
        | _ when pth = EcCoreLib.CI_Witness.p_witness ->
          hyps, circuit_uninit env (f_.f_ty)
        | _ -> 
        begin match EcFol.op_kind (destr_op f_ |> fst) with
          | Some `True -> 
            hyps, (circuit_true :> circuit)
            (*hyps, {circ = BWCirc([C.true_]); inps=[]}*)
          | Some `False ->
            hyps, (circuit_false :> circuit)
            (*hyps, {circ = BWCirc([C.false_]); inps=[]}*)
          | _ -> 
            let err = Format.sprintf "Unsupported op kind%s@." (EcPath.tostring pth) in
            raise (CircError err)
        end
        in 
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ
    end
    | Fapp (f, fs) -> 
    (* TODO: find a way to properly propagate int arguments. Done? *)
    begin match f with
      | {f_node = Fop (pth, _)} when op_is_parametric_base env pth -> 
        let hyps, args = List.fold_left_map (arg_of_form) hyps fs in 
        hyps, circuit_of_op_with_args env pth args
      | {f_node = Fop _} when not (List.for_all (fun f -> f.f_ty.ty_node <> EcTypes.tint.ty_node) fs) ->
          doit cache hyps (propagate_integer_arguments f fs)
      | {f_node = Fop _} -> 
      (* Assuming correct types coming from EC *)
      (* FIXME: Add some extra info about errors when something here throws *)
      begin match EcFol.op_kind (destr_op f |> fst), fs with
      | Some `Eq, [f1; f2] -> 
        let hyps, c1 = doit cache hyps f1 in
        let hyps, c2 = doit cache hyps f2 in
        hyps, (circuit_eq c1 c2 :> circuit)
      (* FIXME: Should this be here on inside the module? *)
      | Some `True, [] ->
        hyps, (circuit_true :> circuit)
      | Some `False, [] ->
        hyps, (circuit_false :> circuit)
      | _ -> (* recurse down into definition *)
        let hyps, f_c = doit cache hyps f in
        let hyps, fcs = List.fold_left_map
          (doit cache)
          hyps fs 
        in
        hyps, circuit_compose f_c fcs
      end
      | _ -> 
        let hyps, f_c = doit cache hyps f in
        let hyps, fcs = List.fold_left_map
          (doit cache)
          hyps fs 
        in
        hyps, circuit_compose f_c fcs
    end
      
    | Fquant (qnt, binds, f) -> 
      let binds = List.map (fun (idn, t) -> (idn, gty_as_ty t)) binds in
      let cache = open_circ_lambda_cache env cache binds in
      let hyps, circ = doit cache hyps f in
      begin match qnt with
      | Llambda -> hyps, close_circ_lambda env binds circ 
      | Lforall 
      | Lexists -> raise (CircError "Universal/Existential quantification not supported ")
      (* TODO: figure out how to handle quantifiers *)
      end
    | Fproj (f, i) ->
        let hyps, ftp = doit cache hyps f in
        let ftp = ctuple_of_circuit ~strict:true ftp in 
        hyps, (circuit_tuple_proj ftp i :> circuit)
    | Fmatch  (f, fs, ty) -> raise (CircError "Match not supported")
    | Flet    (lpat, v, f) -> 
      let hyps, vc = doit cache hyps v in
      let cache = update_cache cache lpat vc in
      doit cache hyps f
    | Fpvar   (pv, mem) -> 
      let v = match pv with
      | PVloc v -> v
      (* FIXME: Should globals be supported? *)
      | _ -> raise (CircError "Global vars not supported")
      in hyps, pstate_get pstate v
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
  in 
(*
  let t0 = Unix.gettimeofday () in
  let () = Format.eprintf "Translating form %a@\n" (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f_ in
*)

  let hyps, f_c = doit cache hyps f_ in

(*
  let () = Format.eprintf "Took %.2f s to translate form : %a@." (Unix.gettimeofday () -. t0) 
  (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) f_ in
*)

  f_c


let circuit_of_path (hyps: hyps) (p: path) : circuit =
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
  

let process_instr (hyps: hyps) (mem: memory) (pstate: pstate) (inst: instr) : pstate =
  let env = toenv hyps in
(*   Format.eprintf "[W] Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst;  *)
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) -> 
(*
      Format.eprintf "Assigning form %a to var %s@\n" 
        (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv (LDecl.toenv hyps))) (form_of_expr mem e) v;
*)
      let pstate = update_pstate pstate v (form_of_expr mem e |> circuit_of_form ~pstate hyps) in
      (* Format.eprintf "[W] Took %f seconds@." (Unix.gettimeofday() -. start); *)
      pstate
    | Sasgn (LvTuple (vs), e) ->
      let tp = (form_of_expr mem e |> circuit_of_form ~pstate hyps) |> (ctuple_of_circuit ~strict:true) in
      let comps = circuits_of_circuit_tuple tp in
      let pstate = List.fold_left2 (fun pstate (pv, _ty) c -> 
        let v = match pv with
        | PVloc v -> v
        | _ -> raise (CircError "Global variables not supported")
        in
        update_pstate pstate v c 
        ) pstate vs (comps :> circuit list)
      in 
      pstate
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
  let inputs = List.map (fun {v_name; v_type} -> (create v_name, v_type)) inputs in
  let pstate = open_circ_lambda_pstate env empty_pstate inputs in

  let pstate1 = List.fold_left (process_instr hyps mem) pstate s1 in
  let pstate2 = List.fold_left (process_instr hyps mem) pstate s2 in

  let pstate1 = close_circ_lambda_pstate env pstate1 inputs in 
  let pstate2 = close_circ_lambda_pstate env pstate2 inputs in
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

let pstate_of_prog (hyps: hyps) (mem: memory) (proc: instr list) (invs: variable list) : pstate =
  (*let inps, pstate = initial_pstate_of_vars (toenv hyps) (invs) in*)
  let env = LDecl.toenv hyps in
  let invs = List.map (fun {v_name; v_type} -> (create v_name, v_type)) invs in
  let pstate = open_circ_lambda_pstate env empty_pstate invs in

  let pstate = 
    List.fold_left (process_instr hyps mem) pstate proc
  in
  close_circ_lambda_pstate env pstate invs

(* FIXME: refactor this function *)
let rec circ_simplify_form_bitstring_equality
  ?(mem = mhr) 
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
      let c1 = circuit_of_form ~pstate hyps f1 in
      let c2 = circuit_of_form ~pstate hyps f2 in
      (*Format.eprintf "[W]Testing circuit equivalence for forms:*)
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
  compute ~sign (cbitstring_of_circuit ~strict:true c) (List.map (fun z -> arg_of_zint z) args)

let circ_equiv ?(pcond: circuit option) c1 c2 = 
  let pcond = match pcond with
  | Some c -> let c = cbool_of_circuit ~strict:false c in
    Some c
  | None -> None
  in
  circ_equiv ?pcond c1 c2

let circuit_permute (bsz: int) (perm: int -> int) (c: circuit) : circuit =
  let c = match c with
  | (`CBitstring r, inps) as c -> c
  | _ -> assert false
  in
  (permute bsz perm c :> circuit)

let circuit_mapreduce ?(perm : (int -> int) option) (c: circuit) (w_in: width) (w_out: width) : circuit list = 
  let c = match c, perm with 
  | (`CBitstring _, inps) as c, None -> c
  | (`CBitstring _, inps) as c, Some perm -> permute w_out perm c
  | _ -> assert false
  in
  (decompose w_in w_out c :> circuit list)

type circuit = ExampleInterface.circuit
type pstate = ExampleInterface.PState.pstate
let circuit_to_string (c: circuit) : string = assert false
let pstate_get = pstate_get 
let pstate_get_opt = pstate_get_opt
let pstate_get_all = fun pstate -> List.snd (pstate_get_all pstate)
let circuit_ueq = (fun c1 c2 -> (circuit_eq c1 c2 :> circuit))
let circuit_aggregate = 
  circuit_aggregate

let circuit_aggregate_inps = 
  circuit_aggregate_inputs


let circuit_flatten (c: circuit) = 
  (cbitstring_of_circuit ~strict:false c :> circuit)
