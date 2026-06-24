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

  type inp = int * int
  type model = (int * string) list

  let reg_of_zint ~(size : int) (v : zint) : reg = of_bigint_all ~size (to_zt v)

  let szint_of_reg (r : reg) : zint =
    bools_of_reg r |> sbigint_of_bools |> of_zt

  let uzint_of_reg (r : reg) : zint =
    bools_of_reg r |> ubigint_of_bools |> of_zt

  let equiv ~(pcond : node) (r1 : reg) (r2 : reg) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    CSMT.BWZ.equiv ctx r1 r2 pcond, lazy (CSMT.BWZ.model ctx)

  let sat (n : node) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    CSMT.BWZ.sat ctx n, lazy (CSMT.BWZ.model ctx)

  let valid (n : node) : bool * model Lazy.t =
    let ctx = CSMT.BWZ.create () in
    CSMT.BWZ.valid ctx n, lazy (CSMT.BWZ.model ctx)
end

module CDeps = struct
  include Lospecs.Deps

  type dep = (int, int Set.t) Map.t
  type deps = dep array
  type block_deps = (int * dep) array

  let dep_of_node = fun n -> dep n
  let deps_of_reg = fun r -> deps r

  let block_deps_of_deps (w : int) (d : deps) : block_deps =
    assert (Array.length d mod w = 0);
    Array.init
      (Array.length d / w)
      (fun i ->
        let deps = Array.sub d (i * w) w in
        let block =
          Array.fold_left
            (fun acc m ->
              Map.merge
                (fun _idx d1 d2 ->
                  match d1, d2 with
                  | None, None -> None
                  | None, Some d | Some d, None -> Some d
                  | Some d1, Some d2 -> Some (Set.union d1 d2))
                acc m)
            Map.empty deps
        in
        w, block)

  let block_deps_of_reg (w : int) (r : C.reg) : block_deps =
    let deps = deps_of_reg r in
    block_deps_of_deps w deps

  let pp_dep (fmt : Format.formatter) (d : dep) : unit =
    Map.iter
      (fun id bits ->
        Format.fprintf fmt "%d: " id;
        Set.iter (fun bit -> Format.fprintf fmt "%d " bit) bits;
        Format.fprintf fmt "@\n")
      d

  let pp_deps (fmt : Format.formatter) (d : deps) : unit =
    Array.iteri
      (fun i d -> Format.fprintf fmt "@[<hov 2>[%d]:@\n%a@]@\n" i pp_dep d)
      d

  let pp_block_deps (fmt : Format.formatter) (bd : block_deps) : unit =
    ignore
    @@ Array.fold_left
         (fun idx (w, d) ->
           Format.fprintf fmt "@[<hov 2>[%d..%d]:@\n%a@]@\n" idx
             (idx + w - 1)
             pp_dep d;
           idx + w)
         0 bd

  let dep_var_count (d : deps) : int =
    Set.cardinal
      (Array.fold_left Set.union Set.empty
         (Array.map (fun dep -> Map.keys dep |> Set.of_enum) d))

  let merge_deps (d : deps) : dep =
    match Array.length d with
    | 0 -> Map.empty
    | _ -> Array.reduce merge_deps d

  (* Assumes single_dep, returns range (bot, top) such that valid idxs are bot <= i < top *)
  let dep_ranges (d : deps) : (int, int * int) Map.t =
    let d = merge_deps d in
    Map.map
      (fun ds ->
        ( Set.min_elt_opt ds |> Option.default (-1),
          Set.max_elt_opt ds |> Option.default (-1) ))
      d

  (* Checks that all dependencies of r are in the set inps *)
  (* Each elements of inps is (id, width) *)
  let check_inputs (r : C.reg) (inps : (int * int) list) : bool =
    let ds = deps_of_reg r in
    Array.for_all
      (fun d ->
        Map.for_all
          (fun id b ->
            match List.find_opt (fun (id_, _) -> id = id_) inps with
            | Some (_, b_) -> Set.for_all (fun b -> 0 <= b && b < b_) b
            | None -> false)
          d)
      ds

  (* Checks if the first argument dependencies are contained in the second *)
  let dep_contained (subd : dep) (superd : dep) : bool =
    Map.for_all
      (fun id bits ->
        match Map.find_opt id superd with
        | None -> false
        | Some superbits -> Set.subset bits superbits)
      subd

  let deps_equal (d1 : dep) (d2 : dep) : bool = Map.equal Set.equal d1 d2

  let deps_intersect (d1 : dep) (d2 : dep) : bool =
    not
    @@ Map.for_all
         (fun id bits1 ->
           match Map.find_opt id d2 with
           | None -> true
           | Some bits2 -> Set.is_empty @@ Set.intersect bits1 bits2)
         d1

  let forall_inputs (check : int -> int -> bool) (r : C.reg) : bool =
    let d = deps_of_reg r in
    Array.for_all
      (fun d -> Map.for_all (fun id bs -> Set.for_all (check id) bs) d)
      d

  let rename_inputs (renamer : int * int -> (int * int) option) (r : C.reg) :
      C.reg =
    C.Reg.maps
      (fun (id, b) ->
        Option.map (fun (id, b) -> C.input (id, b)) (renamer (id, b)))
      r

  let excise_bit ?renamings (n : C.node) : C.node * (int, int * int) Map.t =
    realign_inputs ?renamings n
end

(* ==================================================================== *)
(* Circuit interface, built directly on the lospecs backend.            *)
(* ==================================================================== *)
(* -------------------------------------------------------------------- *)
(* Module Types *)
(* -------------------------------------------------------------------- *)
type ctype =
  | CArray of {width : int; count : int}
  | CBitstring of int
  | CTuple of ctype list

type cval = {reg : C.reg; type_ : ctype}

type cinput = {
  type_ : ctype;
  id : int;
  name : string; (* source-level name, for counter-model display *)
}

type circuit = {cval : cval; inputs : cinput list}
type model = C.model

(* -------------------------------------------------------------------- *)
(* Exceptions *)
(* -------------------------------------------------------------------- *)
type circconstructor =
  | Slice of {slice_size : int; bitstring_size : int; offset : int}
  | SliceSet of {slice_size : int; bitstring_size : int; offset : int}
  | AGet of {container_size : int; index : int}
  | ASet of {container_size : int; index : int}
  | Get of {bitstring_size : int; index : int}
  | And
  | Or
  | Ite
  | Eq
  | Eqs

type lowcircerror =
  | MissingPVFromState
  | CircInputUnificationFailure of (cinput * cinput)
  | CircTyConversionFailure
  | CircConstructorInvalidArguments of circconstructor
  | CircComposeInvalidArguments
  | CircComposeBadNumberOfArguments of {expected : int; received : int}
  | CircEquivNonBoolPCond
  | CircSmtNonBoolCirc
  | CircComputeBadNumberOfArguments of {expected : int; received : int}
  | CircComputeInvalidArguments of int
  | CloseWithoutLambda

exception LowCircError of lowcircerror

let lowcircerror (err : lowcircerror) = raise (LowCircError err)

(* -------------------------------------------------------------------- *)
(* Helper functions *)
(* -------------------------------------------------------------------- *)

let pp_reg fmt r =
  let r = C.Reg.to_list r in
  List.iter (fun n -> Format.fprintf fmt "%a@." (fun fmt -> C.pp_node fmt) n) r

let cval_of_zint ~(size : int) (i : zint) : cval =
  {reg = C.reg_of_zint ~size i; type_ = CBitstring size}

let circuit_of_zint ~(size : int) (i : zint) : circuit =
  {cval = cval_of_zint ~size i; inputs = []}

(* Booleans are 1-bit bitstrings; [cbool] is the soft constructor for
     building such values (there is no distinct [CBool] constructor). *)
let cbool : ctype = CBitstring 1

let rec size_of_ctype (t : ctype) : int =
  match t with
  | CBitstring n -> n
  | CArray {width; count} -> width * count
  | CTuple tys -> List.sum (List.map size_of_ctype tys)

(* -------------------------------------------------------------------- *)
(* Pretty printers *)
(* -------------------------------------------------------------------- *)
let rec pp_ctype (fmt : Format.formatter) (t : ctype) : unit =
  match t with
  | CArray {width; count} -> Format.fprintf fmt "Array(%d@%d)" count width
  | CTuple szs ->
    Format.fprintf fmt "Tuple(%a)"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.pp_print_string fmt ", ")
         pp_ctype)
      szs
  | CBitstring w -> Format.fprintf fmt "Bitstring@%d" w

let pp_cinput (fmt : Format.formatter) (inp : cinput) : unit =
  Format.fprintf fmt "Input(id: %d, type = %a)" inp.id pp_ctype inp.type_

let pp_cval (fmt : Format.formatter) (c : cval) : unit =
  Format.fprintf fmt "Circ(%a)" pp_ctype c.type_

let pp_circuit (fmt : Format.formatter) ({cval; inputs} : circuit) : unit =
  Format.fprintf fmt "@[<hov 2>Circuit:@\nOut type %a@\nInputs: %a@]" pp_cval
    cval
    (fun fmt inputs ->
      List.iter (fun inp -> Format.fprintf fmt "%a@\n" pp_cinput inp) inputs)
    inputs

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

  let arg_of_circuit c = `Circuit c
  let arg_of_zint z = `Constant z
  let arg_of_circuits cs = `List cs
  let arg_of_init f = `Init f

  let pp_arg fmt arg : unit =
    match arg with
    | `Circuit c -> Format.fprintf fmt "%a" pp_circuit c
    | `Constant i -> Format.fprintf fmt "Constant: %s" (to_string i)
    | `Init f -> Format.fprintf fmt "Init: Type of f(0): %a" pp_circuit (f 0)
    | `List cs ->
      Format.fprintf fmt "@[<hov 2> Circuit list: @\n%a@]"
        (fun fmt cs -> List.iter (Format.fprintf fmt "%a@\n" pp_circuit) cs)
        cs
end

open CArgs

(* -------------------------------------------------------------------- *)
(* Translation state *)
(* -------------------------------------------------------------------- *)
module TranslationState = struct
  type state = {
    circs : circuit Mid.t;
    lambdas : cinput list list; (* actually a stack *)
    pv_ids : (ident * symbol, ident) Map.t;
        (* can be changed to int Msym.t if needed *)
    gstate : EcGState.gstate;
  }

  let create_state (gstate : EcGState.gstate) : state =
    {
      circs = Mid.empty;
      lambdas = [];
      pv_ids = Map.empty;
      (* can be changed to int Msym.t if needed *)
      gstate;
    }

  (* Debug log through the gstate's registered notifiers. *)
  let log (st : state) (s : string) : unit =
    EcGState.notify `Debug (lazy s) st.gstate

  let update_state_pv (st : state) (m : memory) (s : symbol) (c : circuit) :
      state =
    match Map.find_opt (m, s) st.pv_ids with
    | Some id -> {st with circs = Mid.add id c st.circs}
    | None ->
      let id = EcIdent.create s in
      {
        st with
        pv_ids = Map.add (m, s) id st.pv_ids;
        circs = Mid.add id c st.circs;
      }

  let state_get_pv_opt (st : state) (m : memory) (s : symbol) : circuit option =
    Option.bind
      (Map.find_opt (m, s) st.pv_ids)
      (fun id -> Mid.find_opt id st.circs)

  let state_get_pv (st : state) (m : memory) (pv : symbol) : circuit =
    match state_get_pv_opt st m pv with
    | Some circ -> circ
    | None -> lowcircerror MissingPVFromState

  let state_get_all_pv (st : state) : ((memory * symbol) * circuit) list =
    let pvs = Map.bindings st.pv_ids in
    List.filter_map
      (fun (pv, id) ->
        match Mid.find_opt id st.circs with
        | None -> None
        | Some c -> Some (pv, c))
      pvs

  let state_get_all_memory (st : state) (m : memory) : (symbol * circuit) list =
    List.filter_map
      (fun ((m_, s), c) -> if m = m_ then Some (s, c) else None)
      (state_get_all_pv st)

  let update_state (st : state) (id : ident) (c : circuit) : state =
    {st with circs = Mid.add id c st.circs}

  let state_get_opt (st : state) (id : ident) : circuit option =
    Mid.find_opt id st.circs

  let state_get (st : state) (id : ident) : circuit = Mid.find id st.circs

  let state_bindings (st : state) : (ident * circuit) list =
    Mid.bindings st.circs

  let state_lambdas (st : state) : cinput list =
    st.lambdas |> List.rev |> List.flatten

  let state_is_closed (st : state) : bool = List.is_empty st.lambdas

  let state_close_circuit (st : state) ({cval; inputs} : circuit) : circuit =
    {
      cval;
      inputs = List.fold_left (fun inps lamb -> lamb @ inps) inputs st.lambdas;
    }

  let map_state_var (f : ident -> circuit -> circuit) (st : state) : state =
    {st with circs = Mid.mapi f st.circs}

  let cinput_of_type (name : [`Idn of ident | `Str of string]) (t : ctype) :
      cinput * circuit =
    let name =
      match name with
      | `Idn id -> id
      | `Str s -> EcIdent.create s
    in
    ( {id = name.id_tag; type_ = t; name = EcIdent.name name},
      {
        cval =
          {
            reg = C.Reg.input_of_size ~id:name.id_tag (size_of_ctype t);
            type_ = t;
          };
        inputs = [];
      } )

  (* Circuit lambdas, for managing inputs *)
  let open_circ_lambda (st : state) (bnds : (ident * ctype) list) : state =
    let inps, cs =
      List.map
        (fun (id, t) ->
          log st
          @@ Format.asprintf "Opening circuit lambda for ident: (%s, %d)@."
               (name id) (tag id);
          let inp, c = cinput_of_type (`Idn id) t in
          inp, (id, c))
        bnds
      |> List.split
    in
    {
      st with
      lambdas = inps :: st.lambdas;
      circs =
        List.fold_left (fun circs (id, c) -> Mid.add id c circs) st.circs cs;
    }

  let open_circ_lambda_pv (st : state) (bnds : ((memory * symbol) * ctype) list)
      : state =
    let st, bnds =
      List.fold_left_map
        (fun st ((m, s), t) ->
          match Map.find_opt (m, s) st.pv_ids with
          | Some id -> st, (id, t)
          | None ->
            let id = EcIdent.create s in
            {st with pv_ids = Map.add (m, s) id st.pv_ids}, (id, t))
        st bnds
    in
    open_circ_lambda st bnds

  let close_circ_lambda (st : state) : state =
    match st.lambdas with
    | [] -> lowcircerror CloseWithoutLambda
    | inps :: lambdas ->
      {
        st with
        lambdas;
        circs =
          Mid.map
            (fun {cval; inputs = cinputs} -> {cval; inputs = inps @ cinputs})
            st.circs;
      }

  let circ_lambda_oneshot
      (st : state)
      (bnds : (ident * ctype) list)
      (c : state -> circuit) : circuit =
    let st' = open_circ_lambda st bnds in
    let {cval; inputs} = c st' in
    {cval; inputs = List.hd st'.lambdas @ inputs}
end

(* Inputs helper functions *)
let merge_inputs (cs : cinput list) (ds : cinput list) : cinput list =
  (*     if List.for_all2 (fun {id=id1; type_=ct1} {id=id2; type_=ct2} -> id1 = id2 && ct1 = ct2) cs ds then cs  *)
  if cs = ds then cs else cs @ ds

let merge_inputs_list (cs : cinput list list) : cinput list =
  List.fold_right merge_inputs cs []

let unify_inputs_renamer (target : cinput list) (inps : cinput list) :
    C.inp -> C.node option =
  let map =
    List.fold_left2
      (fun map inp1 inp2 ->
        match inp1, inp2 with
        | ( {type_ = CBitstring w; id = id_tgt},
            {type_ = CBitstring w'; id = id_orig} )
          when w = w' ->
          List.fold_left
            (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map)
            map
            (List.init w (fun i -> i))
        | ( {type_ = CArray {width = w; count = n}; id = id_tgt},
            {type_ = CArray {width = w'; count = n'}; id = id_orig} )
          when w = w' && n = n' ->
          List.fold_left
            (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map)
            map
            (List.init (w * n) (fun i -> i))
        | {type_ = CTuple tys; id = id_tgt}, {type_ = CTuple tys'; id = id_orig}
          when List.for_all2 ( = ) tys tys' ->
          let w = List.sum (List.map size_of_ctype tys) in
          List.fold_left
            (fun map i -> Map.add (id_orig, i) (C.input (id_tgt, i)) map)
            map
            (List.init w (fun i -> i))
        | _ -> lowcircerror (CircInputUnificationFailure (inp1, inp2)))
      Map.empty target inps
  in
  fun inp -> Map.find_opt inp map

(* Renames circuit2 inputs to match circuit 1 *)
let unify_inputs (target : cinput list) ({cval; inputs} : circuit) : cval =
  let map_ = unify_inputs_renamer target inputs in
  {cval with reg = C.Reg.maps map_ cval.reg}

let circuit_input_compatible ({cval; _} : circuit) (cinput : cinput) : bool =
  match cval.type_, cinput with
  | CBitstring n, {type_ = CBitstring n'} when n = n' -> true
  | CArray {width = w; count = n}, {type_ = CArray {width = w'; count = n'}}
    when w = w' && n = n' ->
    true
  | CTuple szs, {type_ = CTuple szs'} when List.all2 ( = ) szs szs' -> true
  | _ -> false

(* Circuit tuples *)
let circuit_tuple_proj ({cval; inputs} : circuit) (i : int) =
  let r, tys =
    match cval with
    | {reg = r; type_ = CTuple tys} -> r, tys
    | _ -> assert false (* Programming error *)
  in
  let idx, ty = List.takedrop i tys in
  let ty = List.hd ty in
  let idx = List.fold_left ( + ) 0 (List.map size_of_ctype idx) in
  {cval = {reg = C.Reg.extract r idx (size_of_ctype ty); type_ = ty}; inputs}

let circuit_tuple_of_circuits (cs : circuit list) : circuit =
  let tys = List.map (fun (c : circuit) -> c.cval.type_) cs in
  let reg = C.Reg.concat (List.map (fun (c : circuit) -> c.cval.reg) cs) in
  let inputs = List.map (fun (c : circuit) -> c.inputs) cs in
  {cval = {reg; type_ = CTuple tys}; inputs = merge_inputs_list inputs}

let circuits_of_circuit_tuple ({cval; inputs = tpinps} : circuit) : circuit list
    =
  let tp, szs =
    match cval with
    | {reg = tp; type_ = CTuple szs} -> tp, szs
    | _ -> assert false (* Programming error *)
  in
  snd
  @@ List.fold_left_map
       (fun idx ty ->
         let sz = size_of_ctype ty in
         ( idx + sz,
           {cval = {reg = C.Reg.extract tp idx sz; type_ = ty}; inputs = tpinps}
         ))
       0 szs

(* Convert a circuit's output to a given circuit type *)
let convert_type (t : ctype) ({cval = {type_; _} as cval; _} as c : circuit) :
    circuit =
  if t = type_ then c
  else if size_of_ctype t = size_of_ctype type_ then
    {c with cval = {cval with type_}}
  else lowcircerror CircTyConversionFailure

let can_convert_input_type (t1 : ctype) (t2 : ctype) : bool =
  size_of_ctype t1 = size_of_ctype t2

let input_of_ctype
    ?(name : [`Str of string | `Idn of ident] = `Str "input")
    (ct : ctype) : circuit =
  let id, nm, reg =
    match name with
    | `Str name ->
      let id = EcIdent.create name |> tag in
      id, name, C.Reg.input_of_size ~id (size_of_ctype ct)
    | `Idn idn ->
      let id = idn.id_tag in
      id, EcIdent.name idn, C.Reg.input_of_size ~id (size_of_ctype ct)
  in
  {cval = {reg; type_ = ct}; inputs = [{id; type_ = ct; name = nm}]}

let new_input_circuit ?(name = `Str "input") (ty : ctype) : cval * cinput =
  let {cval; inputs} = input_of_ctype ~name ty in
  cval, List.hd inputs

let circuit_true =
  {cval = {reg = C.Reg.singleton C.true_; type_ = cbool}; inputs = []}

let circuit_false =
  {cval = {reg = C.Reg.singleton C.false_; type_ = cbool}; inputs = []}

let circuit_and
    ({cval = c; inputs = cinputs} : circuit)
    ({cval = d; inputs = dinps} : circuit) =
  if c.type_ = d.type_ then
    {
      cval = {reg = C.land_ c.reg d.reg; type_ = c.type_};
      inputs = merge_inputs cinputs dinps;
    }
  else lowcircerror @@ CircConstructorInvalidArguments And

let circuit_or
    ({cval = c; inputs = cinputs} : circuit)
    ({cval = d; inputs = dinps} : circuit) =
  if c.type_ = d.type_ then
    {
      cval = {reg = C.lor_ c.reg d.reg; type_ = c.type_};
      inputs = merge_inputs cinputs dinps;
    }
  else lowcircerror @@ CircConstructorInvalidArguments Or

let circuit_not ({cval = c; inputs} : circuit) =
  {cval = {c with reg = C.lnot_ c.reg}; inputs}

let circuit_is_free (f : circuit) : bool = List.is_empty f.inputs

let circuit_ite ~(c : circuit) ~(t : circuit) ~(f : circuit) : circuit =
  let inputs =
    match c, t, f with
    | {inputs = []; _}, {inputs = []; _}, {inputs = []; _} -> []
    | _ -> assert false
  in
  let c =
    match c.cval.type_ with
    | CBitstring 1 -> C.Reg.node_of_reg c.cval.reg
    | _ -> assert false
  in
  let res_r = C.ite c t.cval.reg f.cval.reg in
  match t.cval.type_, f.cval.type_ with
  | CBitstring nt, CBitstring nf when nt = nf ->
    {cval = {reg = res_r; type_ = t.cval.type_}; inputs}
  | CArray {width = wt; count = nt}, CArray {width = wf; count = nf}
    when wt = wf && nt = nf ->
    {cval = {reg = res_r; type_ = t.cval.type_}; inputs}
  | CTuple szs_t, CTuple szs_f when List.all2 ( = ) szs_t szs_f ->
    {cval = {reg = res_r; type_ = t.cval.type_}; inputs}
  | _ -> lowcircerror @@ CircConstructorInvalidArguments Ite

let circuit_eq (c : circuit) (d : circuit) : circuit =
  match c.cval.type_, d.cval.type_ with
  | CArray _, CArray _ | CTuple _, CTuple _ | CBitstring _, CBitstring _ ->
    {
      cval =
        {reg = C.reg_eq c.cval.reg d.cval.reg |> C.Reg.singleton; type_ = cbool};
      inputs = merge_inputs c.inputs d.inputs;
    }
  | _ -> lowcircerror @@ CircConstructorInvalidArguments Eq

(* Ignore types, do extensionally over bits, return the circuits evaluating to the condition *)
let circuit_eqs
    ({cval = c; inputs = cinputs} : circuit)
    ({cval = d; inputs = dinps} : circuit) : circuit list =
  let inputs = merge_inputs cinputs dinps in

  if size_of_ctype c.type_ <> size_of_ctype d.type_ then
    lowcircerror @@ CircConstructorInvalidArguments Eqs;

  let cs = C.Reg.to_list c.reg in
  let ds = C.Reg.to_list d.reg in
  List.map2
    (fun c d ->
      let r = C.node_eq c d |> C.Reg.singleton in
      {cval = {reg = r; type_ = cbool}; inputs})
    cs ds

let circuit_compose (c : circuit) (args : circuit list) : circuit =
  begin
    try
      if
        not
          (List.for_all2
             (fun c cinput -> circuit_input_compatible c cinput)
             args c.inputs)
      then lowcircerror CircComposeInvalidArguments
    with Invalid_argument _ ->
      lowcircerror
      @@ CircComposeBadNumberOfArguments
           {expected = List.length c.inputs; received = List.length args}
  end;
  let map =
    List.fold_left2
      (fun map {id} c -> Map.add id c map)
      Map.empty c.inputs
      (List.map (fun (a : circuit) -> a.cval) args)
  in
  let map_ (id, idx) =
    let cval = Map.find_opt id map in
    Option.bind cval (fun c ->
        match c.type_ with
        | CArray _ | CTuple _ | CBitstring _ -> begin
          try Some (C.Reg.get c.reg idx) with Invalid_argument _ -> None
        end)
  in

  let cval = {c.cval with reg = C.Reg.maps map_ c.cval.reg} in
  let inputs =
    merge_inputs_list (List.map (fun (a : circuit) -> a.inputs) args)
  in
  {cval; inputs}

(* Fresh arbitrary value (used for [witness] and unknown values) *)
let circuit_uninit (t : ctype) : circuit =
  let {cval; _} = input_of_ctype ~name:(`Str "uninit") t in
  {cval; inputs = []}

let circ_equiv
    ?(pcond : circuit option)
    ({cval = c1; inputs = inps1} : circuit)
    ({cval = c2; inputs = inps2} : circuit) : bool * C.model Lazy.t =
  let pcond = Option.map (convert_type cbool) pcond in
  (* Try to convert to bool *)
  let pcc =
    match pcond with
    | Some {cval = {reg = b; type_ = CBitstring 1}; inputs = pcinputs} ->
      C.map (unify_inputs_renamer inps1 pcinputs) (C.Reg.node_of_reg b)
    | None -> C.true_
    | _ -> lowcircerror CircEquivNonBoolPCond
  in
  (* This throws, but we let it propagate upwards *)
  let c2 = unify_inputs inps1 {cval = c2; inputs = inps2} in
  if c1.type_ = c2.type_ then C.equiv ~pcond:pcc c1.reg c2.reg
  else false, lazy []

let circ_sat ({cval = c; _} : circuit) : bool * C.model Lazy.t =
  let c =
    match c with
    | {type_ = CBitstring 1; reg} -> C.Reg.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
  in
  C.sat c

let circ_valid ({cval = c; _} : circuit) : bool * C.model Lazy.t =
  let c =
    match c with
    | {type_ = CBitstring 1; reg} -> C.Reg.node_of_reg reg
    | _ -> lowcircerror CircSmtNonBoolCirc
  in
  C.valid c

(* Inputs mean different things depending on circuit type *)
(* Allow unaligned slices *)
let circuit_slice ~(size : int) ({cval = c; inputs} : circuit) (offset : int) :
    circuit =
  try
    {
      cval = {reg = C.Reg.extract c.reg offset size; type_ = CBitstring size};
      inputs;
    }
  with Invalid_argument _ ->
    lowcircerror
    @@ CircConstructorInvalidArguments
         (Slice {slice_size = size; bitstring_size = C.Reg.length c.reg; offset})

(* Slice by container index *)
(* Does not type check *)
let circuit_slice_insert
    ({cval = orig_c; inputs = orig_inps} : circuit)
    (idx : int)
    ({cval = new_c; inputs = new_inps} : circuit) : circuit =
  try
    {
      cval = {orig_c with reg = C.Reg.insert orig_c.reg idx new_c.reg};
      inputs = merge_inputs orig_inps new_inps;
    }
  with Invalid_argument _ ->
    lowcircerror
    @@ CircConstructorInvalidArguments
         (SliceSet
            {
              slice_size = C.Reg.length new_c.reg;
              bitstring_size = C.Reg.length orig_c.reg;
              offset = idx;
            })

(* 
     Takes a circuit and uses dependency analysis to separate it into 
     subcircuits corresponding to the output bits
     
     In particular, equivalence between two circuits is equivalent 
     to equivalence between the subcircuits 

     Implicitly flattens everything to bitstrings
  *)
let fillet_circuit ({cval = c; inputs = inps} : circuit) : circuit list =
  let r = c.reg |> C.Reg.to_list in
  List.map
    (fun n ->
      let new_inps =
        List.map
          (fun {id = _; type_; name} ->
            {id = EcIdent.create "_" |> tag; type_; name})
          inps
      in
      let renamings =
        List.combine
          (List.map (fun {id} -> id) inps)
          (List.map (fun {id} -> id) new_inps)
        |> List.to_seq |> Map.of_seq
      in
      let renamings = fun v -> Map.find_opt v renamings in
      let n', shifts = CDeps.excise_bit ~renamings n in

      let new_inps =
        List.filter_map
          (fun {id; name; _} ->
            match Map.find_opt id shifts with
            | Some (low, hi) ->
              Some {id; type_ = CBitstring (hi - low + 1); name}
            | None -> None)
          new_inps
      in
      {cval = {reg = C.Reg.singleton n'; type_ = cbool}; inputs = new_inps})
    r

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
    (checks : circuit list) : circuit list =
  (* Order by dependencies *)
  let checks =
    if sort then begin
      let checks =
        List.map
          (fun (c : circuit) ->
            c, C.(CDeps.dep_of_node (Reg.node_of_reg c.cval.reg)))
          checks
      in
      let checks =
        List.stable_sort
          (fun (_, d1) (_, d2) ->
            let m1 = Map.keys d1 |> Set.of_enum |> Set.min_elt_opt in
            let m2 = Map.keys d2 |> Set.of_enum |> Set.min_elt_opt in
            match m1, m2 with
            | None, None -> 0
            | None, Some _ -> -1
            | Some _, None -> 1
            | Some m1, Some m2 ->
              let c1 = Int.compare m1 m2 in
              if c1 = 0 then
                Int.compare
                  (Map.find m1 d1 |> Set.min_elt_opt |> Option.default (-1))
                  (Map.find m1 d2 |> Set.min_elt_opt |> Option.default (-1))
              else c1)
          checks
      in
      checks
    end
    else
      List.map
        (fun (c : circuit) ->
          c, C.(CDeps.dep_of_node (Reg.node_of_reg c.cval.reg)))
        checks
  in

  let rec doit
      (acc : circuit list)
      ((cur, d) : circuit * CDeps.dep)
      (cs : (circuit * CDeps.dep) list) : circuit list =
    match cs with
    | [] -> cur :: acc
    | (c, d') :: cs -> begin
      match mode with
      | `ByEq when CDeps.deps_equal d d' -> doit acc (circuit_and cur c, d) cs
      | `BySub when CDeps.(dep_contained d d') ->
        doit acc (circuit_and cur c, d') cs
      | `BySub when CDeps.(dep_contained d' d) ->
        doit acc (circuit_and cur c, d) cs
      | _ -> doit (cur :: acc) (c, d') cs
    end
  in

  match checks with
  | [] -> []
  | c :: cs -> doit [] c cs

let attach_compatible_pres
    ?(mode : [`Cont | `Eq | `Int] = `Cont)
    (pres : (circuit * CDeps.dep) list)
    (post : circuit) : circuit =
  let d = C.(CDeps.dep_of_node (Reg.node_of_reg post.cval.reg)) in
  let compat_pres =
    List.filteri
      (fun _i (_c, pre_dep) ->
        match mode with
        | `Cont -> CDeps.dep_contained pre_dep d
        | `Eq -> CDeps.deps_equal pre_dep d
        | `Int -> CDeps.deps_intersect pre_dep d)
      pres
  in
  let compat_pres = List.fst compat_pres in
  let pre = List.fold_left circuit_and circuit_true compat_pres in
  circuit_or (circuit_not pre) post

let sublimate_inputs ({cval = c; inputs = cinputs} : circuit) : circuit =
  assert (c.type_ = cbool);
  let node_c = C.Reg.node_of_reg c.reg in
  let node_c, shifts = CDeps.excise_bit node_c in
  let inps =
    List.filter_map
      (fun {id; name; _} ->
        match Map.find_opt id shifts with
        | Some (low, hi) -> Some {id; type_ = CBitstring (hi - low + 1); name}
        | None -> None)
      cinputs
  in
  {cval = {reg = C.Reg.singleton node_c; type_ = cbool}; inputs = inps}

let collapse_lanes (lanes : circuit list) =
  (* Circuit structural equality after renaming *)
  let ( === ) (c1 : cval) (c2 : cval) : bool =
    let n', _ = C.Reg.node_of_reg c1.reg |> CDeps.excise_bit in
    let n, _ = C.Reg.node_of_reg c2.reg |> CDeps.excise_bit in
    C.equal n n'
  in
  let rec collapse (acc : circuit list) (cur : circuit) (cs : circuit list) :
      circuit list =
    match cs with
    | [] -> cur :: acc
    | c :: cs ->
      if c.cval === cur.cval then collapse acc cur cs
      else collapse (cur :: acc) c cs
  in
  let rec doit (cs : circuit list) : circuit list =
    match cs with
    | [] -> []
    | [c] -> [c]
    | c :: cs -> begin
      try
        let idx, _ = List.findi (fun _ c2 -> c.cval === c2.cval) cs in
        let idx = idx + 1 in
        (* Length of the list to merge *)
        if idx = 1 then doit (collapse [] c cs)
        else if (List.length cs + 1) mod idx != 0 then c :: cs
        else
          let cs =
            List.chunkify idx (c :: cs) |> List.map (List.reduce circuit_and)
          in
          doit cs
      with Not_found -> c :: cs
    end
  in
  doit lanes

(* 
    - Attaches preconditions to postconditions
    - Realigns inputs
    - Checks for structural equality of circuits
    - SMT check for any remainings ones
   *)
let fillet_tauts (pres : circuit list) (posts : circuit list) : bool =
  (* Assumes everything is single bit outputs. *)
  let posts =
    List.filter_map
      (fun (post : circuit) ->
        if C.equal (C.Reg.node_of_reg post.cval.reg) C.true_ then None
        else Some post)
      posts
  in

  match posts with
  | [] -> true
  | posts ->
    if
      (not (List.for_all (fun (c : circuit) -> c.cval.type_ = cbool) pres))
      || not (List.for_all (fun (c : circuit) -> c.cval.type_ = cbool) posts)
    then lowcircerror CircSmtNonBoolCirc;
    let pres =
      List.map
        (fun (c : circuit) ->
          c, CDeps.dep_of_node (C.Reg.node_of_reg c.cval.reg))
        pres
    in
    let posts = List.map (attach_compatible_pres ~mode:`Int pres) posts in
    let posts = collapse_lanes posts in

    List.map
      (fun post ->
        let post = sublimate_inputs post in
        fst (circ_valid post))
      posts
    |> List.for_all identity

let compute ~(sign : bool) (c : circuit) (args : arg list) : zint option =
  begin
    match c.cval.type_ with
    | CBitstring _ -> ()
    | _ -> assert false
  end;

  if List.compare_lengths args c.inputs <> 0 then
    lowcircerror
    @@ CircComputeBadNumberOfArguments
         {expected = List.length c.inputs; received = List.length args};

  let args =
    List.map2i
      (fun i arg inp ->
        match arg, inp with
        | `Circuit c, inp when circuit_input_compatible c inp -> c
        | `Constant i, {type_ = CBitstring size} ->
          {
            cval = {reg = C.reg_of_zint ~size i; type_ = CBitstring size};
            inputs = [];
          }
        | _ -> lowcircerror @@ CircComputeInvalidArguments i)
      args c.inputs
  in
  match circuit_compose c args with
  | {cval = {reg = r; type_ = CBitstring _}; inputs = []} ->
    Some (if sign then C.szint_of_reg r else C.uzint_of_reg r)
  | {inputs = _ :: _; _} -> assert false (* Should not happen *)
  | _ -> assert false (* Should not happen *)

let circuit_aggregate (cs : circuit list) : circuit =
  let inps = List.map (fun (c : circuit) -> c.inputs) cs in
  let cs = List.map (fun (c : circuit) -> c.cval.reg) cs in
  let reg = C.Reg.concat cs in
  let inps = merge_inputs_list inps in
  {cval = {reg; type_ = CBitstring (C.Reg.length reg)}; inputs = inps}

let input_aggregate_renamer (inps : cinput list) :
    cinput * (C.inp -> C.node option) =
  let new_id = create "aggregated" |> tag in
  let size, map =
    List.fold_left
      (fun (size, map) inp ->
        match inp with
        | {type_ = CBitstring w; id} -> size + w, Map.add id (size, w) map
        | {type_ = CArray {width = w; count = n}; id} ->
          size + (w * n), Map.add id (size, w * n) map
        | {type_ = CTuple tys; id} ->
          let w = List.sum @@ List.map size_of_ctype tys in
          size + w, Map.add id (size, w) map)
      (0, Map.empty) inps
  in
  ( {type_ = CBitstring size; id = new_id; name = "aggregated"},
    fun (id, bit) ->
      let base_sz = Map.find_opt id map in
      Option.bind base_sz (fun (base, sz) ->
          let idx = bit + base in
          if bit >= 0 && bit < sz then Some (C.input (new_id, idx)) else None) )

let circuit_aggregate_inputs ({cval = c; inputs} : circuit) : circuit =
  let inp, renamer = input_aggregate_renamer inputs in
  {cval = {c with reg = C.Reg.maps renamer c.reg}; inputs = [inp]}

let circuit_from_spec
    ?(name : symbol option)
    ((arg_tys, ret_ty) : ctype list * ctype)
    (spec : Lospecs.Ast.adef) : circuit =
  let c args = C.circuit_of_specification args spec in

  let name =
    match name with
    | Some name -> name ^ "_spec_input"
    | None -> "spec_input"
  in

  let cinputs, inps =
    List.mapi
      (fun i ty ->
        let nm = name ^ "_" ^ string_of_int i in
        let id = EcIdent.create nm |> tag in
        let size : int = size_of_ctype ty in
        C.Reg.input_of_size ~id size, {type_ = ty; id; name = nm})
      arg_tys
    |> List.split
  in
  let reg = c cinputs in
  {cval = {reg; type_ = ret_ty}; inputs = inps}

(* -------------------------------------------------------------------- *)
(* Bit-vector operators *)
(* -------------------------------------------------------------------- *)
module BVOps = struct
  let bvget (c : circuit) (i : int) : circuit =
    match c with
    | {cval = {reg; type_ = CBitstring n}; inputs} when 0 <= i && i < n -> begin
      try
        {
          cval = {reg = C.Reg.singleton (C.Reg.get reg i); type_ = cbool};
          inputs;
        }
      with Invalid_argument _ ->
        lowcircerror
          (CircConstructorInvalidArguments (Get {bitstring_size = n; index = i}))
    end
    | _ -> assert false (* programming error *)

  let circuit_of_parametric_bvop (op : EcDecl.crb_bvoperator) (args : arg list)
      : circuit =
    match op.kind with
    | `ASliceGet (((_, Some _), (_, Some _)), (_, Some m)) -> begin
      match args with
      (* Assume type checking from EC? *)
      | [`Circuit ({cval = {type_ = CArray _; _}; _} as circ); `Constant i] ->
      begin
        match circ.cval.type_ with
        | CArray {width = w'; count = n'} ->
          circuit_slice ~size:m
            {
              cval = {reg = circ.cval.reg; type_ = CBitstring (w' * n')};
              inputs = circ.inputs;
            }
            (to_int i)
        | _ -> assert false (* Does not happen, guarded by match above *)
      end
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `ASliceSet (((_, Some _), (_, Some _)), (_, Some _)) -> begin
      match args with
      | [
       `Circuit ({cval = {type_ = CArray _; _}; _} as arr_circ);
       `Constant i;
       `Circuit ({cval = {type_ = CBitstring _; _}; _} as bs_circ);
      ] -> begin
        match arr_circ.cval.type_, bs_circ.cval.type_ with
        | CArray _, CBitstring _ ->
          circuit_slice_insert arr_circ (to_int i) bs_circ
        (* If this fails, then we have an inconsistent binding, should be prevented by EC *)
        | _ -> assert false
      end
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `Extract ((_, Some _), (_, Some w_out), aligned) -> begin
      match args with
      | [`Circuit ({cval = {type_ = CBitstring _; _}; _} as c); `Constant i] ->
        circuit_slice ~size:w_out c ((if aligned then w_out else 1) * to_int i)
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `Insert ((_, Some _), (_, Some _)) -> begin
      match args with
      | [
       `Circuit ({cval = {type_ = CBitstring _; _}; _} as orig_c);
       `Constant i;
       `Circuit ({cval = {type_ = CBitstring _; _}; _} as new_c);
      ] ->
        circuit_slice_insert orig_c (to_int i) new_c
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `Map ((_, Some w_i), (_, Some w_o), (_, Some n)) -> begin
      match args with
      | [
       `Circuit cf;
       `Circuit {cval = {reg = arr; type_ = CArray {width = _; count = _}}; _};
      ] ->
        let circs, inps =
          List.split
          @@ List.map
               (fun c ->
                 match circuit_compose cf [c] with
                 | {cval = {type_ = CBitstring _; reg}; inputs} -> reg, inputs
                 (* Should be caught by EC typechecking + binding correctness *)
                 | _ -> assert false)
               (List.init n (fun i ->
                    {
                      cval =
                        {
                          reg = C.Reg.extract arr (i * w_i) w_i;
                          type_ = CBitstring w_i;
                        };
                      inputs = [];
                    }))
        in
        (* Inputs of all components should match after map *)
        if not (List.for_all (( = ) (List.hd inps)) inps) then
          (* Should be caught by EC typechecking + binding correctness *)
          assert false;
        let inputs = List.hd inps in
        {
          cval =
            {reg = C.Reg.concat circs; type_ = CArray {width = w_o; count = n}};
          inputs;
        }
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `Get (_, Some _) -> begin
      match args with
      | [`Circuit c; `Constant i] -> bvget c (EcBigInt.to_int i)
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `AInit ((_, Some n), (_, Some w_o)) -> begin
      match args with
      | [`Init init_f] ->
        let cs = List.init n init_f in
        let cinputs = List.map (fun (c : circuit) -> c.inputs) cs in
        let circs =
          List.map
            (fun (c : circuit) ->
              match c.cval with
              | {type_ = CBitstring _; reg = r} when C.Reg.length r = w_o -> r
              (* Invalid type for init component *)
              (* Should be caught by EC typechecking + binding correctness *)
              | _ -> assert false)
            cs
        in
        (* Inputs should be uniform across components after mapping *)
        if not (List.for_all (( = ) (List.hd cinputs)) cinputs) then
          (* Should be caught by EC typechecking + binding correctness *)
          assert false;
        let inputs = List.hd cinputs in
        {
          cval =
            {type_ = CArray {width = w_o; count = n}; reg = C.Reg.concat circs};
          inputs;
        }
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | `Init (_, Some w) -> begin
      match args with
      | [`Init init_f] ->
        let cs = List.init w init_f in
        let cinputs = List.map (fun (c : circuit) -> c.inputs) cs in
        let circs =
          List.map
            (fun (c : circuit) ->
              match c.cval with
              | {type_ = CBitstring 1; reg = b} -> C.Reg.node_of_reg b
              (* Return type should be bool (= bit) for components *)
              (* Should be caught by EC typechecking + binding correctness *)
              | _ -> assert false)
            cs
        in
        if not (List.for_all (( = ) (List.hd cinputs)) cinputs) then
          (* Should be caught by EC typechecking + binding correctness *)
          assert false;
        let inputs = List.hd cinputs in
        {cval = {type_ = CBitstring w; reg = C.Reg.of_list circs}; inputs}
      (* Should be caught by EC typechecking + binding correctness *)
      | _ -> assert false
    end
    | _ -> assert false
  (* Should not happen because calls should be guarded by call to op_is_parametric_bvop *)

  let circuit_of_bvop (op : EcDecl.crb_bvoperator) : circuit =
    let binop ?isz2 ?out (isz1 : int) (f : C.reg -> C.reg -> C.reg) : circuit =
      let isz2 = Option.default isz1 isz2 in
      let out = Option.default isz1 out in
      let {reg = c1; _}, inp1 = new_input_circuit (CBitstring isz1) in
      let {reg = c2; _}, inp2 = new_input_circuit (CBitstring isz2) in
      {cval = {type_ = CBitstring out; reg = f c1 c2}; inputs = [inp1; inp2]}
    in
    let cmp (size : int) (f : C.reg -> C.reg -> C.node) : circuit =
      let {reg = c1; _}, inp1 = new_input_circuit (CBitstring size) in
      let {reg = c2; _}, inp2 = new_input_circuit (CBitstring size) in
      {
        cval = {type_ = cbool; reg = C.Reg.singleton (f c1 c2)};
        inputs = [inp1; inp2];
      }
    in
    let unop (isz : int) (out : int) (f : C.reg -> C.reg) : circuit =
      let {reg = c1; _}, inp1 = new_input_circuit (CBitstring isz) in
      {cval = {type_ = CBitstring out; reg = f c1}; inputs = [inp1]}
    in
    match op with
    | {kind = `Add (_, Some size)} -> binop size C.add_dropc
    | {kind = `Sub (_, Some size)} -> binop size C.sub_dropc
    | {kind = `Mul (_, Some size)} -> binop size C.umull
    | {kind = `Div ((_, Some size), false)} -> binop size C.udiv
    | {kind = `Div ((_, Some size), true)} -> binop size C.sdiv
    | {kind = `Rem ((_, Some size), false)} -> binop size C.umod
    | {kind = `Rem ((_, Some size), true)} -> binop size C.smod
    | {kind = `Shl (_, Some size)} -> binop size (C.shift ~side:`L ~sign:`L)
    | {kind = `Shr ((_, Some size), false)} ->
      binop size (C.shift ~side:`R ~sign:`L)
    | {kind = `Shr ((_, Some size), true)} ->
      binop size (C.shift ~side:`R ~sign:`A)
    | {kind = `Shls ((_, Some size1), (_, Some size2))} ->
      binop ~isz2:size2 size1 (C.shift ~side:`L ~sign:`L)
    | {kind = `Shrs ((_, Some size1), (_, Some size2), false)} ->
      binop ~isz2:size2 size1 (C.shift ~side:`R ~sign:`L)
    | {kind = `Shrs ((_, Some size1), (_, Some size2), true)} ->
      binop ~isz2:size2 size1 (C.shift ~side:`R ~sign:`A)
    | {kind = `Rol (_, Some size)} -> binop size C.rol
    | {kind = `Ror (_, Some size)} -> binop size C.ror
    | {kind = `And (_, Some size)} -> binop size C.land_
    | {kind = `Or (_, Some size)} -> binop size C.lor_
    | {kind = `Xor (_, Some size)} -> binop size C.lxor_
    | {kind = `Not (_, Some size)} -> unop size size C.lnot_
    | {kind = `Opp (_, Some size)} -> unop size size C.opp
    | {kind = `Lt ((_, Some size), false)} -> cmp size C.ult
    | {kind = `Lt ((_, Some size), true)} -> cmp size C.slt
    | {kind = `Le ((_, Some size), false)} -> cmp size C.ule
    | {kind = `Le ((_, Some size), true)} -> cmp size C.sle
    | {kind = `Extend ((_, Some size), (_, Some out_size), false)} ->
      assert (size <= out_size);
      unop size out_size (C.uextend ~size:out_size)
    | {kind = `Extend ((_, Some size), (_, Some out_size), true)} ->
      assert (size <= out_size);
      unop size out_size (C.sextend ~size:out_size)
    | {kind = `Truncate ((_, Some size), (_, Some out_sz))} ->
      assert (size >= out_sz);
      unop size out_sz (fun c -> C.Reg.truncate c out_sz)
    | {kind = `Concat ((_, Some sz1), (_, Some sz2), (_, Some szo))} ->
      assert (sz1 + sz2 = szo);
      binop ~isz2:sz2 ~out:szo sz1 C.Reg.append
    | {kind = `A2B (((_, Some w), (_, Some n)), (_, Some m))} ->
      assert (n * w = m);
      let c, inp = new_input_circuit (CArray {width = w; count = n}) in
      {cval = {c with type_ = CBitstring m}; inputs = [inp]}
    | {kind = `B2A ((_, Some m), ((_, Some w), (_, Some n)))} ->
      assert (n * w = m);
      let c, inp = new_input_circuit (CBitstring m) in
      {cval = {c with type_ = CArray {width = w; count = n}}; inputs = [inp]}
    | {
        kind =
          ( `ASliceGet _ | `ASliceSet _ | `Extract _ | `Insert _ | `Map _
          | `AInit _ | `Get _ | `Init _ );
      }
    | _ ->
      assert false (* Should be guarded by call to op_is_bvop *)
end

(* -------------------------------------------------------------------- *)
(* Array operators *)
(* -------------------------------------------------------------------- *)
module ArrayOps = struct
  let array_get (c : circuit) (i : int) : circuit =
    match c with
    | {cval = {reg = c; type_ = CArray {width = w; count = n}}; inputs} -> begin
      try
        {cval = {type_ = CBitstring w; reg = C.Reg.extract c (i * w) w}; inputs}
      with Invalid_argument _ ->
        lowcircerror
        @@ CircConstructorInvalidArguments
             (AGet {container_size = n; index = i})
    end
    | _ -> assert false (* Programming error *)

  let array_set (a : circuit) (pos : int) (bs : circuit) : circuit =
    match a, bs with
    | ( {cval = {reg = arr; type_ = CArray {width = w; count = n}}; inputs},
        {cval = {reg = bs; type_ = CBitstring w'}; inputs = cinputs} ) -> begin
      try
        assert (w = w');
        {
          cval =
            {
              type_ = CArray {width = w; count = n};
              reg = C.Reg.insert arr (pos * w) bs;
            };
          inputs = merge_inputs inputs cinputs;
        }
      with Invalid_argument _ ->
        lowcircerror
        @@ CircConstructorInvalidArguments
             (ASet {container_size = n; index = pos})
    end
    | _ -> assert false (* Programming error *)

  let array_oflist (circs : circuit list) (dfl : circuit) (len : int) : circuit
      =
    let inps = List.map (fun (c : circuit) -> c.inputs) circs in
    let circs = List.map (fun (c : circuit) -> c.cval) circs in
    let dif = len - List.length circs in
    assert (dif >= 0);
    let circs = circs @ List.init dif (fun _ -> dfl.cval) in
    let inps = if dif > 0 then inps @ [dfl.inputs] else inps in
    let circs =
      List.map
        (function
          | {type_ = CBitstring _; reg = r} -> r
          (* Should be caught by EC typechecking + binding correctness *)
          | _ -> assert false)
        circs
    in
    {
      cval =
        {
          type_ = CArray {width = C.Reg.length (List.hd circs); count = len};
          reg = C.Reg.concat circs;
        };
      inputs = merge_inputs_list inps;
    }
end

include CArgs
include TranslationState

let reset_backend_state () = C.HCons.clear ()
