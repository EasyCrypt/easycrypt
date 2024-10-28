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

(* -------------------------------------------------------------------- *)
type width = int

type asize = { wordsize: int; nelements: width; }

let size_of_asize (sz : asize) : int =
  sz.wordsize * sz.nelements

(* type deps = ((int * int) * int C.VarRange.t) list *)
(* Inputs to circuit functions: 
   Either bitstring of fixed size
   Or Array of fixed number of elements each of a fixed size *)
type cinput = 
  (* Name of input + size *)
  | BWInput of (ident * int)
  (* Name of array + (array size x element size) *)
  | BWAInput of (ident * asize)

let asize_to_string (asize : asize) : string =
  Format.sprintf "%d[%d]" asize.wordsize asize.nelements

let cinput_to_string = function
  | BWInput (idn, w) -> Format.sprintf "(%s, %d)" (name idn) w
  | BWAInput (idn, sz) -> Format.sprintf "(%s, %s)" (name idn) (asize_to_string sz)

(* Checks whether inputs are the same up to renaming *)
let cinput_equiv (a: cinput) (b: cinput) : bool =
  match a, b with
  | BWInput (_, w1), BWInput (_, w2) -> w1 = w2 
  | BWAInput (_, sz1), BWAInput (_, sz2) -> sz1 = sz2 
  | _ -> false

let is_bwinput = function
  | BWInput _ -> true
  | _ -> false

let is_bwainput = function
  | BWAInput _ -> true
  | _ -> false

let destr_bwinput = function
  | BWInput (idn, w) -> (idn, w)
  | _ -> assert false

let destr_bwainput = function
  | BWAInput (idn, sz) -> (idn, sz)
  | _ -> assert false

let bwinput_of_size (w : width) : cinput =
  let name = "bw_input" in
  BWInput (create name, w)

let bwainput_of_size ~(nelements : width) ~(wordsize : width) : cinput =
  let name = "arr_input" in
  BWAInput (create name, { nelements; wordsize; })

(* # of total bits of input *)
let size_of_cinput = function
  | BWInput (_, w) -> w
  | BWAInput (_, sz) -> size_of_asize sz

(* name of input *)
let ident_of_cinput = function
  | BWInput (idn, _) -> idn
  | BWAInput (idn, _) -> idn

(* Base circuit, represents body of a circuit function *)
type circ = 
  | BWCirc of C.reg
  | BWArray of C.reg array

let is_bwcirc = function
  | BWCirc _ -> true
  | _ -> false

let is_bwarray = function
  | BWArray _ -> true
  | _ -> false

let destr_bwcirc = function
  | BWCirc r -> r
  | _ -> assert false

let destr_bwarray = function
  | BWArray a -> a
  | _ -> assert false

(* # of total bits of output *)
let size_of_circ = function
  | BWCirc r -> List.length r
  | BWArray a -> Array.fold_left (+) 0 (Array.map List.length a)

(* Simple representation *)
let circ_to_string = function 
  | BWCirc r -> Format.sprintf "BWCirc@%d" (List.length r)
  | BWArray a -> Format.sprintf "BWArray[%d[%d]]" (a.(0) |> List.length) (Array.length a)

(* Checks whether the output shapes are the same
  FIXME: should be enough to compare first element of the array
  if we enforce arrays to be homogeneous 
  If not then array input should change *)
let circ_shape_equal (c1: circ) (c2: circ) = 
  match c1, c2 with
  | BWArray r1, BWArray r2 -> Array.for_all2 (fun a b -> List.compare_lengths a b = 0) r1 r2
  | BWCirc r1, BWCirc r2 -> List.compare_lengths r1 r2 = 0
  | _ -> false

(* Circuit functions:
    circ <- body with (input i) nodes for the inputs 
    inps <- inputs to the function 
*)
type circuit = {
  circ: circ;
  inps: cinput list
}

(* Representation of body + inputs *)
let circuit_to_string (c: circuit) =
  Format.sprintf "%s | %s" 
    (circ_to_string c.circ)
    (String.concat ", " (List.map cinput_to_string c.inps))

(* Takes a list of inputs and returns the identity function over those inputs *)
(* Useful for renaming or getting a given input shape for a circuit *)
let circ_ident (input: cinput) : circuit = 
  match input with
  | BWInput (idn, w) -> 
    { circ = BWCirc (C.reg ~size:w ~name:(tag idn)); inps = [input]}
  | BWAInput (idn, sz) -> 
    let c = C.reg ~name:(tag idn) ~size:(size_of_asize sz) in
    let c = Array.of_list (List.chunkify sz.wordsize c) in
    assert (Array.length c = sz.nelements);
    { circ = BWArray c; inps=[input]}

(* Checks whether the two circuits have the same inputs up to renaming *)
let input_shape_equal (f: circuit) (g: circuit) : bool = 
  (List.compare_lengths f.inps g.inps = 0) && 
  (List.for_all2 (cinput_equiv) (f.inps) (g.inps))

(* Checks if there are no shared inputs among elements of the list
  That is, the name of each input to each circuit in the list does not 
  appear as an input in another element in the list *)
let inputs_indep (fs: circuit list) : bool =
  let s = List.map (fun c -> Set.of_list (List.map ident_of_cinput c.inps)) fs in
  let c = List.fold_left (fun acc s -> acc + (Set.cardinal s)) 0 s in
  let s = List.fold_left Set.union Set.empty s in
  (Set.cardinal s) = c

(* Checks whether the given circuit can be applied to the given input 
  That is, if the shape of the output of the circ 
  matches the shape of the input *)
let match_arg (inp: cinput) (val_: circ) : bool =
  match inp, val_ with
  | BWInput (_, w), BWCirc r when List.compare_length_with r w = 0 ->
    true
  | BWAInput (_, sz), BWArray a
    when Array.length a = sz.nelements
      && Array.for_all (fun v -> List.compare_length_with v sz.wordsize = 0) a ->
      true
  | _ -> Format.eprintf "inp: %s does not match %s@."
    (cinput_to_string inp) (circ_to_string val_); false

(* 
   Fully applies a function to a list of constant arguments
   returning a constant value
*) 
let apply (f: circuit) (args: circ list) : circ = 
  assert (List.compare_lengths f.inps args = 0);
  let () = try
    assert (List.for_all2 match_arg f.inps args);
  with Assert_failure _ as e -> 
    Format.eprintf "%s@." (Printexc.get_backtrace ());
    Format.eprintf "Error applying on %s@." (circuit_to_string f);
    Format.eprintf "Arguments: @.";
    List.iter (Format.eprintf "%s@.") (List.map circ_to_string args);
    raise e
  in
  let args = List.combine f.inps args in
  let map_ = fun (id, i) ->
    let vr = List.find_opt (function 
      | BWInput (idn, _), _ when id = tag idn -> true
      | BWAInput (idn, _), _ when id = tag idn -> true
      | _ -> false 
      ) args
    in Option.bind vr 
      (function 
      | BWInput (_, w), BWCirc r -> List.at_opt r i
      | BWAInput (_, sz), BWArray a -> 
        let ia, iw = (i / sz.wordsize), (i mod sz.wordsize) in
        let res = try 
          List.at_opt a.(ia) iw
        with Invalid_argument _ ->
          None
        in res
      | _ -> assert false
        )
  in
  match f.circ with
  | BWCirc r -> BWCirc (C.maps map_ r)
  | BWArray rs -> BWArray (Array.map (C.maps map_) rs)

(* Given an input returns a new input with the same shape *)
let fresh_cinput (c: cinput) : cinput = 
  match c with
  | BWInput (idn, w) -> BWInput (fresh idn, w)
  | BWAInput (idn, sz) -> BWAInput (fresh idn, sz)

(* Given a circuit function returns a new circuit function 
   with new names for the inputs (with the needed substituition
   being done in the body of the function as well)              *)
let fresh_inputs (c: circuit) : circuit =
  let new_inps = List.map fresh_cinput c.inps in
  let ni_circs = List.map (fun inp -> (circ_ident inp).circ) new_inps in
  {circ = apply c ni_circs; inps = new_inps}

(* Returns a copy of a list of circuits modified so that there are no 
   collisions between the inputs (= all the inputs have different names) *)
let dist_inputs (c: circuit list) : circuit list = 
  let rec doit (c: circuit list) (s: cinput Set.t) : circuit list =
    match c with
    | [] -> []
    | f::fs -> 
      let c = Set.cardinal s in
      let s2 = Set.of_list f.inps in
      let c = c + (Set.cardinal s2) in
      let s = Set.union s s2 in
      (if (Set.cardinal s) = c then f else fresh_inputs f)::(doit fs s)
  in
  match c with
  | [] -> []
  | c::[] -> [c]
  | c::cs -> c::(doit cs (Set.of_list c.inps))

(* -------------------------------------------------------------------- *)
exception CircError of string

let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circuit.lookup_bitstring_size env t with
  | Some w -> w
  | None -> let err = Format.asprintf "No bitvector binding for type %a@."
  (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in 
  raise (CircError err)

(* returns size of array and underlying element type if array type, otherwise None *)
let destr_array_type (env: env) (t: ty) : (int * ty) option = 
  match t.ty_node with
  | Tconstr (p, [et]) -> 
    begin match EcEnv.Circuit.lookup_array_path env p with
    | Some {size; _} -> Some (size, et)
    | None -> None
    end
  | _ -> None

let shape_of_array_type (env: env) (t: ty) : (int * int) = 
  match t.ty_node with
  | Tconstr (p, [et]) -> 
    begin match EcEnv.Circuit.lookup_array_path env p with
    | Some {size; _} -> size, width_of_type env et
    | None -> assert false
    end
  | _ -> assert false

(* Given an EC type with the correct bindings returns a circuit input
   matching the shape of that type *)
let cinput_of_type ?(idn: ident option) (env: env) (t: ty) : cinput = 
  let name = "from_type" in
  let idn = match idn with
  | Some idn -> idn
  | None -> create name 
  in
  match destr_array_type env t with
  | None -> BWInput (idn, width_of_type env t)
  | Some (nelements, t) ->
    let wordsize = width_of_type env t in
    BWAInput (idn, { nelements; wordsize })

(* given f(inps1), g(inps2) returns h(inps1,inps2) = f(a) @ g(b)
   where @ denotes concatenation of circuits *)
let circuit_concat (c: circuit) (d: circuit) : circuit =
  let d = if inputs_indep [c;d] then d else fresh_inputs d in
  match c.circ, d.circ with
  | BWCirc ccirc, BWCirc dcirc -> 
    {circ=BWCirc(ccirc @ dcirc); inps=c.inps @ d.inps}
  | _ -> assert false

(* Same as above but concatenates arrays of bitwords *)
let circuit_array_concat (c: circuit) (d: circuit) : circuit =
  let d = if inputs_indep [c;d] then d else fresh_inputs d in
  match c.circ, d.circ with
  | BWArray carr, BWArray darr -> 
    {circ=BWArray(Array.concat [carr; darr]); inps=c.inps @ d.inps}
  | _ -> assert false

let (++) : circuit -> circuit -> circuit = circuit_concat
let (+@) : circuit -> circuit -> circuit = circuit_array_concat

(* Given f_i(inps_i) returns h(inps_1, ...) = f_1(inps_1) @ ... 
  aka given a list of functions returns a function that concatenates 
  their outputs, given all their inputs *)
let circuit_aggregate (c: circuit list) : circuit =
  List.reduce (++) c

let circuit_array_aggregate (c: circuit list) : circuit =
  List.reduce (+@) c


(* To be removed and replaced by a combination of other operations *)
let circuit_bwarray_set ~(nelements : width) ~(wordsize : width) (i: int) : circuit =
  assert (nelements > i);
  let arr_inp = BWAInput (create "arr_input", { nelements; wordsize; }) in
  let bw_inp = BWInput (create "bw_input", wordsize) in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let bw_id = (ident_of_cinput bw_inp).id_tag in
  let out = Array.init nelements (fun ja ->
    if ja = i then List.init wordsize (fun j -> C.input (bw_id, j))
    else List.init wordsize (fun j -> C.input (arr_id, ja*wordsize + j))) in
  {circ= BWArray (out); inps = [arr_inp; bw_inp]}

(* Same as above *)
let circuit_bwarray_get ~(nelements : width) ~(wordsize : width) (i: int) : circuit =
  assert (nelements > i);
  let arr_inp = BWAInput (create "arr_input", { nelements; wordsize; }) in
  let out = List.init wordsize (fun j -> C.input ((ident_of_cinput arr_inp).id_tag, j + wordsize*i)) in
  {circ=BWCirc (out); inps=[arr_inp]}


  
(* Function composition for circuits *)
(* Reduces to application if arguments are 0-ary *)
let compose (f: circuit) (args: circuit list) : circuit = 
  (* assert (List.compare_lengths f.inps args = 0); *)
  (* Length comparison should be done in apply *)
  let args = 
    dist_inputs args
  in
  {circ=apply f (List.map (fun c -> c.circ) args); 
  inps=List.reduce (@) (List.map (fun c -> c.inps) args)}


(* 
  Unifies input to allow for equivalence testing 
*)
let merge_inputs (fs: circuit list) : circuit list option =
  match fs with
  | [] -> Some [] 
  | [f] -> Some [f]
  | f::gs -> 
    if not @@ List.for_all (fun g -> input_shape_equal f g) gs 
    then None 
    else
      let new_inps = List.map (fun inp -> circ_ident inp) f.inps in
      Some (List.map (fun f -> compose f new_inps) fs)

(* Identity on bitstrings, 
   breaks a function returning an array into a list of functions returning 
   components *)
let circuits_of_circuit (c: circuit) : circuit list =
  match c.circ with
  | BWCirc r -> [c]
  | BWArray a -> 
    List.map (fun r -> {circ=BWCirc r; inps=c.inps}) (Array.to_list a)

(* Ident on bitstrings, flattens arrays into bitstrings *)
let circuit_flatten (c: circuit) : circuit =
  match c.circ with
  | BWCirc _ -> c
  | BWArray a -> 
    {circ=BWCirc(Array.fold_right (@) a []); inps=c.inps}

(* Chunks a bitstring into an array of bitstrings, each of size w *)
let circuit_bw_split (c: circuit) (w: int) : circuit = 
  match c.circ with
  | BWArray _ -> assert false
  | BWCirc r -> 
    let nk = List.length r in
    assert (nk mod w = 0);
    let rs = List.chunkify w r |> Array.of_list in
    {circ=BWArray rs; inps = c.inps}

(* Zero-extends a bitstring *)
let circuit_bw_zeroextend (c: circuit) (w: int) : circuit = 
  assert(size_of_circ c.circ <= w);
  let r = destr_bwcirc c.circ in
  let zs = List.init (w - size_of_circ c.circ) (fun _ -> C.true_) in
  {c with circ = BWCirc(r @ zs)}

(* Given a list of inputs inp_i, returns a new input inp 
   plus a list of circuit functions f_i such that 
   f_i(inp) = inp_i (in shape) and all the f_i are independent *)
let bus_of_cinputs (inps: cinput list) : circ list * cinput =
  let idn = create "bus" in
  let bsize = List.map (size_of_cinput) inps |> List.sum in
  let r = C.reg ~size:bsize ~name:(tag idn) in
  let rec doit (r: C.reg) (cs: cinput list) : circ list =
    match r, cs with
    | [], [] -> []
    | [], _ -> assert false
    | _, [] -> assert false
    | _, BWInput (_, w)::cs -> let r1, r2 = List.takedrop w r in
      (BWCirc r1)::(doit r2 cs)
    | _, BWAInput (_, sz)::cs -> let r1, r2 = List.takedrop (size_of_asize sz) r in
      let r1 = List.chunkify sz.wordsize r1 |> Array.of_list in
      (BWArray r1)::(doit r2 cs)
  in
  doit r inps, BWInput (idn, bsize)

(* Transforms the input for the circuit given into a big bitstring 
   (by concat + flatten of the previous inputs )*)
let circuit_aggregate_inps (c: circuit) : circuit = 
  match c.inps with
  | [] -> c
  | _ -> let circs, inp = bus_of_cinputs c.inps in
    {circ=apply c circs; inps=[inp]}

(* 
  Array slices
  out_sz = size of out array (base size = input array base size)
  i = start_index
*)
let circuit_array_sliceget ~(wordsize : width) (arr_sz : width) (out_sz: width) (i: int) : circuit = 
  assert (arr_sz >= out_sz + i);
  let arr_inp = bwainput_of_size ~nelements:arr_sz ~wordsize in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let out = Array.init out_sz (fun ja ->
    List.init wordsize (fun jl -> 
      C.input (arr_id, (i+ja)*wordsize + jl)
    )
  ) in
  {circ = BWArray out; inps=[arr_inp]}
  
(* 
  Array slice assignment
  out_sz = size of array to assign (base size = input array base size)
  i = start_index
*)
let circuit_array_sliceset ~(wordsize : width) (arr_sz : width) (out_sz: width) (i: int) : circuit = 
  assert (arr_sz >= out_sz + i);
  let arr_inp = bwainput_of_size ~nelements:arr_sz ~wordsize in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let new_arr_inp = bwainput_of_size ~nelements:out_sz ~wordsize in
  let new_arr_id = (ident_of_cinput new_arr_inp).id_tag in
  let out = Array.init arr_sz (fun ja ->
    if ja < i || ja >= (i + out_sz) then 
      List.init wordsize (fun jl -> C.input (arr_id, ja*wordsize + jl))
    else
      List.init wordsize (fun jl -> C.input (new_arr_id, (ja-i)*wordsize + jl))
  ) in
  {circ = BWArray out; inps = [arr_inp; new_arr_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwarray_slice_get (arr_sz: width) (el_sz: width) (acc_sz: int) (i: int) : circuit =
  assert (arr_sz*el_sz >= i + acc_sz);
  let arr_inp = bwainput_of_size ~nelements:arr_sz ~wordsize:el_sz in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let out = List.init acc_sz (fun j -> C.input (arr_id, i+j)) in
  {circ=BWCirc out; inps=[arr_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwarray_slice_set (arr_sz: width) (el_sz: width) (acc_sz: int) (i: int) : circuit =
  assert (arr_sz*el_sz >= i + acc_sz);
  let bw_inp = bwinput_of_size acc_sz in
  let bw_id = (ident_of_cinput bw_inp).id_tag in
  let arr_inp = bwainput_of_size ~nelements:arr_sz ~wordsize:el_sz in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let out = Array.init arr_sz (fun ja ->
    List.init el_sz (fun jl -> 
      let idx = ja*el_sz + jl in
      if idx < i || idx >= (i + acc_sz) then
        C.input (arr_id, idx)
      else
        C.input (bw_id, idx - i)
    )
  ) in
  {circ=BWArray (out); inps=[arr_inp; bw_inp]}

(* Input for splitting function w.r.t. dependencies *)
let input_of_tdep (n: int) (bs: int Set.t) : _ * cinput = 
  let temp_symbol = "tdep_ident" in
  let m = Set.cardinal bs in
  let id = create temp_symbol in
  let map_ = Set.to_seq bs |> List.of_seq in
  let map_ = List.map (fun a -> (n, a)) map_ in
  let map_ = List.combine map_ (List.init m (fun i -> C.input (id.id_tag, i))) in
  let map_ = Map.of_seq (List.to_seq map_) in
  map_, BWInput (id, m)
  
let inputs_of_tdep (td: HL.tdeps) :  _ * cinput list =
  Map.foldi (fun n bs (map_, inps) -> let map_2, inp = input_of_tdep n bs in
    (Map.union map_ map_2, inp::inps)) td (Map.empty, [])   

(* 
  f : BV1 -> BV2 
  a : BV1 Arr
  returns: BV2 Array = mapping f over a
*)
let circuit_map (f: circuit) (a: circuit) : circuit =
  let a, inps = destr_bwarray a.circ, a.inps in
  let r = Array.map (fun r -> apply f [BWCirc r]) a in
  let r = Array.map (destr_bwcirc) r in
  {circ = BWArray r; inps}

(* Partitions into blocks of type n -> m *)
let circuit_mapreduce (c: circuit) (n:int) (m:int) : circuit list =
  let tm = Unix.gettimeofday () in
  Format.eprintf "[W] Beginning dependency analysis@.";
  let const_inp = BWInput (create "const", n) in
  let c = circuit_flatten c in
  let c = if List.compare_length_with c.inps 1 > 0 then
    circuit_aggregate_inps c 
    else c
  in
  let r = destr_bwcirc c.circ in
  let deps = HL.deps r in
  let deps = HL.split_deps m deps in

  Format.eprintf "%d@." (List.length deps);

  assert (HL.block_list_indep deps);
  assert (List.for_all (HL.check_dep_width n) (List.snd deps));
(*  assert ((List.sum (List.map size_of_cinput c.inps)) mod n = 0);*)

  Format.eprintf "[W] Dependency analysis complete after %f seconds@."
  (Unix.gettimeofday () -. tm);
  
  let doit (db: HL.tdblock) (c: C.reg) : circuit * C.reg =
    let res, c = List.takedrop (fst db) c in
    let map_, inps = inputs_of_tdep (snd db) in
    let res = C.maps (fun a -> Map.find_opt a map_) res in
    {circ = BWCirc res; inps}, c
  in
  let cs, c = List.fold_left (fun (cs, c) bd -> let r, c = doit bd c in
    (r::cs, c)) ([], destr_bwcirc c.circ) deps in
  assert (List.length c = 0);
  List.map (function
    | {circ=BWCirc r; inps=[BWInput (idn, w)]}
      -> {circ=BWCirc (C.uextend ~size:m r); inps=[BWInput (idn, n)]}
    | {circ=BWCirc r; inps=[]}
      -> {circ=BWCirc (C.uextend ~size:m r); inps=[const_inp]}
    | c -> Format.eprintf "Failed for %s@." (circuit_to_string c) ; assert false)
  cs

(* Build a circuit function that takes an input n bits wide and permutes 
  it in blocks of w bits by the permutation given by f 
  Expects that w | n and that f|[n/w] is a bijection *)
let circuit_permutation (n: int) (w: int) (f: int -> int) : circuit = 
  assert (n mod w = 0);
  assert ( List.init (n/w) f |> Set.of_list |> Set.map f |> Set.cardinal = (n/w));
  let inp = bwinput_of_size n in
  let inp_circ = circ_ident inp in
  let cblocks = destr_bwcirc inp_circ.circ in 
  let cblocks = List.chunkify w cblocks in 
  let cblocks = List.mapi (fun i _ -> List.nth cblocks (f i)) cblocks |> List.flatten in
  {circ=BWCirc(cblocks); inps=[inp]}
  
(* -------------------------------------------------------------------- *)
(* Basis for hardcoded circuit gen *)
let specifications : (string, Lospecs.Ast.adef) Map.t Lazy.t =
  Lazy.from_fun (fun () ->
    let specs = Filename.concat (List.hd Lospecs.Config.Sites.specs) "avx2.spec" in
    let specs = C.load_from_file ~filename:specs in
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
  | None -> Format.eprintf "No operator for path: %s@."
    (let a,b = EcPath.toqsymbol p in List.fold_right (fun a b -> a ^ "." ^ b) a b);
    assert false 


let circuit_from_spec (env: env) (p : path) : circuit = 
  let _, temp_name = (EcPath.toqsymbol p) in
  let temp_name = temp_name ^ "_spec_input" in
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
    (C.reg ~name:id.id_tag ~size, BWInput (id, size))
    ) argtys |> List.split in
  {circ = BWCirc(circ cinps); inps}
    
  
module BaseOps = struct
  let temp_symbol = "temp_circ_input"
  
  let is_of_int (env: env) (p: path) : bool = 
    match EcEnv.Circuit.reverse_bitstring_operator env p with
    | Some (_, `OfInt) -> true
    | _ -> false

  let circuit_of_baseop (env: env) (p: path) : circuit = 
    match EcEnv.Circuit.lookup_bvoperator_path env p with
    | Some { kind = `Add size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.add_dropc c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}
    | Some { kind = `Sub size } ->
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.sub_dropc c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Mul  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.umull c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Div (size, false) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.udiv c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Div (size, true) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.sdiv c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Rem (size, false) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.urem c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Rem (size, true) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.srem c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Shl  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`L ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Shr  (size, false) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`R ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Shr  (size, true) } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`R ~sign:`A c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `And  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.land_ c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Or   size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.lor_ c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Not  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.lnot_ c1 ); inps = [BWInput(id1, size)]}

    | Some { kind = `Lt (size, false) } ->
      let id1 = EcIdent.create temp_symbol in
      let id2 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in 
      let c2 = C.reg ~size ~name:id2.id_tag in 
      { circ = BWCirc([C.ugt c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}
    
    | Some { kind = `Lt (size, true) } ->
      let id1 = EcIdent.create temp_symbol in
      let id2 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in 
      let c2 = C.reg ~size ~name:id2.id_tag in 
      { circ = BWCirc([C.sgt c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Le (size, false) } ->
      let id1 = EcIdent.create temp_symbol in
      let id2 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in 
      let c2 = C.reg ~size ~name:id2.id_tag in 
      { circ = BWCirc([C.uge c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}    

    | Some { kind = `Le (size, true) } ->
      let id1 = EcIdent.create temp_symbol in
      let id2 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in 
      let c2 = C.reg ~size ~name:id2.id_tag in 
      { circ = BWCirc([C.sge c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}    

    | Some { kind = `Extend (size, out_size, false) } ->
      assert (size <= out_size);
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.uextend ~size:out_size c1); inps = [BWInput (id1, size)]}

    | Some { kind = `Extend (size, out_size, true) } ->
      assert (size <= out_size);  
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.sextend ~size:out_size c1); inps = [BWInput (id1, size)]}

    | Some { kind = `Truncate (size, out_sz) } ->
      assert (size >= out_sz);
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size:out_sz ~name:id1.id_tag in
      { circ = BWCirc(c1); inps=[BWInput (id1, size)]}

    | Some { kind = `Concat (sz1, sz2, szo) } ->
      assert (sz1 + sz2 = szo);
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size:sz1 ~name:id1.id_tag in
      let id2 = EcIdent.create (temp_symbol) in
      let c2 = C.reg ~size:sz2 ~name:id2.id_tag in
      { circ = BWCirc(c1 @ c2); inps=[BWInput (id1, sz1); BWInput (id2, sz2)]}

    | Some { kind = `A2B ((w, n), m)} ->
      assert (n * w = m);
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size:m ~name:id1.id_tag in
      { circ = BWCirc(c1); inps = [BWAInput (id1, { nelements = n; wordsize = w })]}

    | Some { kind = `B2A (m, (w, n))} ->
      assert (n * w = m);
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size:m ~name:id1.id_tag in
      let c1 = List.chunkify w c1 |> Array.of_list in
      { circ = BWArray(c1); inps=[BWInput(id1, m)]}

    | _ -> raise @@ CircError "Failed to generate op"
    
end

module ArrayOps = struct
  let temp_symbol = "temp_array_input"

  let is_arrayop (env: env) (pth: path) : bool =
    Option.is_some
      (EcEnv.Circuit.reverse_array_operator env pth)
  
  let destr_array_opt (env: env) (pth: path) : crb_array_operator option =
    EcEnv.Circuit.reverse_array_operator env pth
end

let circ_equiv ?(strict=false) (f: circuit) (g: circuit) (pcond: circuit option) : bool = 
  let f, g = 
    if strict then (assert(circ_shape_equal f.circ g.circ); f, g)
    else if size_of_circ f.circ < size_of_circ g.circ then
      circuit_bw_zeroextend f (size_of_circ g.circ), g else
      f, circuit_bw_zeroextend g (size_of_circ f.circ)
  in
  let pcond = match pcond with
  | Some pcond -> pcond
  | None -> {circ = BWCirc [C.true_]; inps = f.inps}
  in
  match merge_inputs [f;g;pcond] with
  | None -> Format.eprintf "Failed to merge inputs@."; false
  | Some [{circ=BWCirc fcirc; _} as f;
    {circ=BWCirc gcirc; _};
    {circ=BWCirc pccirc; _}] ->
    begin
      (List.for_all2 (==) fcirc gcirc) ||
      let module B = (val HL.makeBWZinterface ()) in
      B.circ_equiv fcirc gcirc (List.hd pccirc) 
      (List.map (fun inp -> let a, b = destr_bwinput inp in
      (a.id_tag, b)) f.inps)
      (* Assuming no array inputs for now *)
    end
  | _ -> assert false
  
let circ_check (f: circuit) (pcond: circuit option) : bool =
  let module B = (val HL.makeBWZinterface ()) in
  let f = match f with
  | {circ=BWCirc([f]); _} -> f
  | _ -> raise @@ CircError "Form should only output one bit (bool)"
  in
  match pcond with
  | None -> B.circ_taut f
  | Some {circ=BWCirc([pcond]);_} -> not @@ B.circ_sat @@ (C.and_ pcond (C.neg f))
  | _ -> raise @@ CircError "Precondition should output one bit (bool)"

let circ_sat (f: circuit) (pcond: circuit option): bool = 
  let module B = (val HL.makeBWZinterface ()) in
  let f = match f with
  | {circ=BWCirc([f]); _} -> f
  | _ -> raise @@ CircError "Form should only output one bit (bool)"
  in
  match pcond with
  | Some {circ=BWCirc([pcond]); _} -> B.circ_sat (C.and_ pcond f)
  | None -> B.circ_sat f
  | _ -> raise @@ CircError "pcond should only output one bit (bool)"
  

(* Vars = bindings in scope (maybe we have some other way of doing this? *)

(* FIXME: Refactor this later *)
let op_cache = ref Mp.empty

type pstate = (symbol, circuit) Map.t
type cache  = (ident, (cinput * circuit)) Map.t

(* TODO: Decide if we want to store stuff in the environment or not, 
         if not: remove env argument from recursive calls *)
let circuit_of_form 
  ?(pstate : pstate = Map.empty) (* Program variable values *)
  ?(cache  : cache = Map.empty) (* Let-bindings and such *)
   (hyps    : hyps) 
   (f_      : EcAst.form) 
  : circuit =

  let rec doit (cache: (ident, (cinput * circuit)) Map.t) (hyps: hyps) (f_: form) : hyps * circuit = 
    let env = toenv hyps in
    let redmode = EcReduction.full_red in
    let redmode = {redmode with delta_p = (fun pth ->
      if (EcEnv.Circuit.reverse_operator (LDecl.toenv hyps) pth |> List.is_empty) then
        redmode.delta_p pth
      else
        `No)
    } in
    (* let redmode = {redmode with delta_p = fun _ -> `No} in *)
    let fapply_safe f fs = 
      (* let pp_form = EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env) in *)
      (* Format.eprintf "f: %a@.fs: %a@." pp_form *)
        (* f (fun fmt fs -> List.iter (Format.fprintf fmt "%a, " pp_form) fs) fs; *)
      let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
      (* Format.eprintf "res : %a@." pp_form f; *)
      res
    in

    let int_of_form (f: form) : zint = 
      match f.f_node with 
      | Fint i -> i
      | _ -> destr_int @@ EcCallbyValue.norm_cbv EcReduction.full_red hyps f
    in
    
    match f_.f_node with
    (* hardcoding size for now FIXME *)
    | Fint z -> assert false
      (* env, {circ = BWCirc(C.of_bigint ~size:256 (to_zt z)); inps = []} *)
      (* failwith "Add logic to deal with ints (maybe force conversion?)" *)
      (* hlenv, C.of_bigint ~size:256 (EcAst.BI.to_zt z) *)
    | Fif (c_f, t_f, f_f) -> 
        let hyps, c_c = doit cache hyps c_f in
        let hyps, t_c = doit cache hyps t_f in
        let hyps, f_c = doit cache hyps f_f in
        let () = assert (List.length (destr_bwcirc c_c.circ) = 1) in
        let () = assert (List.is_empty c_c.inps) in
        let () = assert (List.is_empty t_c.inps) in
        let () = assert (List.is_empty f_c.inps) in
        let c_c = List.hd (destr_bwcirc c_c.circ) in
        begin
        match t_c.circ, f_c.circ with
        | BWCirc t_c, BWCirc f_c ->
        hyps, {
          circ = BWCirc (C.ite c_c t_c f_c);
          inps = []; 
        }
        | BWArray t_cs, BWArray f_cs when (Array.length t_cs = Array.length f_cs) ->
          hyps, {
            circ = BWArray (Array.map2 (C.ite c_c) t_cs f_cs);
            inps = []; (* FIXME: check if we want to allow bindings inside ifs *)
          }
        | _ -> assert false
        end
      (* Assumes no quantifier bindings/new inputs within if *)
    | Flocal idn -> 
      begin match Map.find_opt idn cache with
      | Some (inp, circ) -> 
        (* Check if we want = or equiv here FIXME *)
        if (cinput_equiv inp (cinput_of_type env f_.f_ty)) then
        hyps, circ
        else 
          let err = Format.asprintf "Var binding shape %s for %s does not match shape of form type %s@."
           (cinput_to_string inp) idn.id_symb (cinput_of_type env f_.f_ty |> cinput_to_string) in
           raise @@ CircError err
      | None -> 
          let err = Format.asprintf "Var binding not found for %s@." idn.id_symb in 
          raise @@ CircError err
      end
    | Fop (pth, _) -> 
      begin
      match Mp.find_opt pth !op_cache with
      | Some op -> 
        (* Format.eprintf "Using cached op: %s@." (EcPath.tostring pth); *)
        hyps, op
      | None -> 
        (* Format.eprintf "No cache for op: %s@." (EcPath.tostring pth); *)
      if (Option.is_some @@ EcEnv.Circuit.reverse_bvoperator env pth) then
        let circ = BaseOps.circuit_of_baseop env pth in
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ 
      else if (Option.is_some @@ EcEnv.Circuit.reverse_circuit env pth) then
        let circ = circuit_from_spec env pth in
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ
      else
        let hyps, circ = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper ( Some (OP_Plain f)) -> 
          doit cache hyps f
        | _ -> begin match EcFol.op_kind (destr_op f_ |> fst) with
          | Some `True -> 
            hyps, {circ = BWCirc([C.true_]); inps=[]}
          | Some `False ->
            hyps, {circ = BWCirc([C.false_]); inps=[]}
          | _ -> 
            Format.eprintf "%s@." (EcPath.tostring pth); failwith "Unsupported op kind"
        end
        in 
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ
    end
    | Fapp _ -> 
    let (f, fs) = EcCoreFol.destr_app f_ in
    let hyps, res = 
      (* Assuming correct types coming from EC *)
      (* FIXME: add typechecking here ? *)
      match EcEnv.Circuit.reverse_operator env @@ (EcCoreFol.destr_op f |> fst) with
      | `Array ({ size }, `Get) :: _ -> let hyps, res = 
        match fs with
        | [arr; i] ->
          let i = int_of_form i in
          let (_, t) = destr_array_type env arr.f_ty |> Option.get in
          let w = width_of_type env t in
          let hyps, arr = doit cache hyps arr in
          hyps, compose (circuit_bwarray_get ~nelements:size ~wordsize:w (BI.to_int i)) [arr]
        | _ -> raise (CircError "set")
        in hyps, res
      | `Array ({ size }, `Set) :: _ -> let hyps, res = 
        match fs with
        | [arr; i; v] ->
          let i = int_of_form i in
          let w = width_of_type env v.f_ty  in
          let hyps, arr = doit cache hyps arr in
          let hyps, v = doit cache hyps v in
          hyps, compose (circuit_bwarray_set ~nelements:size ~wordsize:w (BI.to_int i)) [arr; v]
        | _ -> raise (CircError "set")
        in hyps, res
      | `Array ({ size }, `OfList) :: _->
        let _, { nelements = n; wordsize = w } = destr_bwainput @@ cinput_of_type env f_.f_ty in
        assert (n = size);
        (* FIXME: have an actual way to get sizes without creating new idents *)
        let wtn, vs = match fs with
          | [wtn; vs] -> wtn, vs 
          | _ -> assert false (* should only be two arguments to of_list *)
        in
        let vs = EcCoreFol.destr_list vs in
        let hyps, vs = List.fold_left_map (doit cache) hyps vs in
        begin match EcCoreFol.is_witness wtn with
        | false -> 
          let hyps, wtn = doit cache hyps wtn in
          assert(List.is_empty wtn.inps && List.for_all (fun c -> List.is_empty c.inps) vs);
          let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
          let wtn = destr_bwcirc wtn.circ in
          let r = Array.init n (fun i -> List.nth_opt vs i |> Option.default wtn) in
          hyps, {circ = BWArray r; inps = []}
        | true -> 
          assert (List.compare_length_with vs n = 0);
          assert (List.for_all (fun c -> List.is_empty c.inps) vs);
          let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
          let r = Array.of_list vs in
          hyps, {circ=BWArray r; inps=[]}
        end
      | `Bitstring ({ size }, `OfInt) :: _ ->
        let i = match fs with
        | f :: _ -> int_of_form f
        | _ -> assert false
        in 
        hyps, { circ = BWCirc (C.of_bigint ~size (to_zt i)); inps = [] }
      | `BvOperator ({ kind = `Extract (size, out_sz) }) :: _ ->
        assert (size >= out_sz);
        let c1, b = match fs with
        | [c; f] -> c, int_of_form f
        | _ -> assert false
        in
        let hyps, c1 = doit cache hyps c1 in
        let c = destr_bwcirc c1.circ in
        let c = List.take out_sz (List.drop (to_int b) c) in
        hyps, { circ = BWCirc(c); inps=c1.inps }
      | `BvOperator ({kind = `Init (size)}) :: _ ->
        let f = match fs with
        | [f] -> f
        | _ -> assert false
        in
        let fs = List.init size (fun i -> fapply_safe f [f_int (of_int i)]) in
        (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)
        let hyps, fs = List.fold_left_map (doit cache) hyps fs in
        hyps, circuit_aggregate fs
      | `BvOperator ({kind = `AInit (arr_sz, bw_sz)}) :: _ ->
        let f = match fs with
        | [f] -> f
        | _ -> assert false
        in
        let fs = List.init arr_sz (fun i -> fapply_safe f [f_int (of_int i)]) in
        (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)
        let hyps, fs = List.fold_left_map (doit cache) hyps fs in
        assert (List.for_all (fun c -> List.is_empty c.inps) fs);
        hyps, {circ = BWArray(Array.of_list (List.map (fun c -> destr_bwcirc c.circ) fs)); inps=[]}

        (* begin *)
        (* match f.f_node with *)
        (* | Fapp _ -> Format.eprintf "Its an Fapp@."; assert false *)
        (* | Fquant (Llambda, _, _) -> Format.eprintf "Its an Flambda@."; assert false *)
        (* | Fop _ -> Format.eprintf "Its an Fop@."; assert false *)
        (* | _ -> Format.eprintf "Its something else @."; assert false *)
        (* end *)
      | `BvOperator ({kind = `Map (sz1, sz2, asz)}) :: _ -> 
        let f, a = match fs with
        | [f; a] -> f, a
        | _ -> assert false
        in 
        let hyps, f = doit cache hyps f in
        let hyps, a = doit cache hyps a in
        hyps, circuit_map f a

      | `BvOperator ({kind = `ASliceGet ((arr_sz, sz1), sz2)}) :: _ ->
        let arr, i = match fs with
        | [arr; i] -> arr, int_of_form i
        | _ -> assert false
        in
        let op = circuit_bwarray_slice_get arr_sz sz1 sz2 (to_int i) in
        let hyps, arr = doit cache hyps arr in
        hyps, compose op [arr]
        
      | `BvOperator ({kind = `ASliceSet ((arr_sz, sz1), sz2)}) :: _ ->
        let arr, i, bv = match fs with
        | [arr; i; bv] -> arr, int_of_form i, bv
        | _ -> assert false
        in
        let op = circuit_bwarray_slice_set arr_sz sz1 sz2 (to_int i) in
        let hyps, arr = doit cache hyps arr in
        let hyps, bv = doit cache hyps bv in
        hyps, compose op [arr; bv]

      | _ -> begin match EcFol.op_kind (destr_op f |> fst), fs with
        | Some `Eq, [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          begin match c1.circ, c2.circ with
          | BWCirc r1, BWCirc r2 -> 
            assert (List.compare_lengths r1 r2 = 0);
            hyps, {circ = BWCirc([C.bvueq r1 r2]); inps=c1.inps @ c2.inps} (* FIXME: check inps here *)
          | BWArray a1, BWArray a2 -> 
            assert (Array.length a1 = Array.length a2);
            assert (Array.for_all2 (fun a b -> (List.compare_lengths a b) = 0) a1 a2);
            let rs = Array.map2 C.bvueq a1 a2 in
            hyps, {circ = BWCirc([C.ands (Array.to_list rs)]); inps = c1.inps @ c2.inps}
          | _ -> assert false
          end
        | Some `True, [] ->
          hyps, {circ = BWCirc([C.true_]); inps=[]}
        | Some `False, [] ->
          hyps, {circ = BWCirc([C.false_]); inps=[]}
        | None, _ -> 
          let hyps, f_c = doit cache hyps f in
          let hyps, fcs = List.fold_left_map
            (doit cache)
            hyps fs 
          in
          hyps, compose f_c fcs
        | _ -> Format.eprintf "Problem at %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f_;
          assert false
        end
      in hyps, res
      
    | Fquant (qnt, binds, f) -> 
      (* FIXME: check if this is desired behaviour for exists and add logic for others *)
      let binds = List.map (fun (idn, t) -> cinput_of_type ~idn env (gty_as_ty t)) binds in
      let cache = List.fold_left 
        (fun cache inp -> 
          let circ = {(circ_ident inp) with inps = []} in
          Map.add (ident_of_cinput inp) (inp, circ) cache) cache binds in
      let hyps, circ = doit cache hyps f in
      begin match qnt with
      | Llambda -> hyps, {circ with inps=binds @ circ.inps} (* FIXME: check input order *)
      | Lforall 
      | Lexists -> assert false
      (* TODO: figure out how to handle quantifiers *)
      end
    | Fproj (f, i) ->
        begin match f.f_node with
        | Ftuple tp ->
          doit cache hyps (tp |> List.drop (i-1) |> List.hd)
        | _ -> failwith "Don't handle projections on non-tuples"
        end
    | Fmatch  (f, fs, ty) -> assert false
    | Flet    (lpat, v, f) -> 
      begin match lpat with
      | LSymbol (idn, ty) -> 
        let hyps, vc = doit cache hyps v in
        let inp = cinput_of_type ~idn env ty in
        let () = assert (match_arg inp vc.circ) in
        let cache = Map.add idn (inp, vc) cache in
        doit cache hyps f
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
        | None -> raise (CircError (Format.sprintf "Uninitialized program variable %s" v))
        (* | None -> let circ = circ_ident (cinput_of_type ~idn:(create "uninit") env f_.f_ty) in *)
          (* {circ with inps=[]} *)
      (* EXPERIMENTAL: allowing unitialized values *)
          (* failwith ("No value for var " ^ v) *)
      in hyps, res
    | Fglob   (id, mem) -> assert false
    | Ftuple  comps -> assert false
    | _ -> failwith "Not yet implemented"

  in 
  let hyps, f_c = doit cache hyps f_ in
  f_c


let circuit_of_path (hyps: hyps) (p: path) : circuit =
  let f = EcEnv.Op.by_path p (toenv hyps) in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> failwith "Invalid operator type"
  in
  circuit_of_form hyps f

let input_of_variable (env:env) (v: variable) : circuit * cinput =
  let idn = create v.v_name in
  let inp = cinput_of_type ~idn env v.v_type in
  {(circ_ident inp) with inps=[]}, inp
  

let pstate_of_variables ?(pstate = Map.empty) (env : env) (vars : variable list) =
  let inps = List.map (input_of_variable env) vars in
  let inpcs, inps = List.split inps in
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) vars in
  let pstate = List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 
  in pstate, inps

let pstate_of_memtype ?pstate (env: env) (mt : memtype) =
  let Lmt_concrete lmt = mt in
  let vars =
    List.filter_map (function 
      | { ov_name = Some name; ov_type = ty } ->
        Some { v_name = name; v_type = ty; }
      | _ -> None
    ) (Option.get lmt).lmt_decl in
  pstate_of_variables ?pstate env vars

let process_instr (hyps: hyps) (mem: memory) ?(cache: cache = Map.empty) (pstate: _) (inst: instr) =
  let env = toenv hyps in
  (* Format.eprintf "[W]Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst; *)
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, ty), e) -> 
      let pstate = Map.add v (form_of_expr mem e |> circuit_of_form ~pstate ~cache hyps) pstate in
      (* Format.eprintf "[W] Took %f seconds@." (Unix.gettimeofday() -. start); *)
      pstate
    | Sasgn (LvTuple (vs), e) -> begin match e.e_node with
      | Etuple (es) -> List.fold_left2 (fun pstate (v, t) e ->
        let v = match v with | PVloc v -> v | _ -> assert false in
        Map.add v (form_of_expr mem e |> circuit_of_form ~pstate ~cache hyps) pstate) pstate vs es
      | _ -> failwith "Case not implemented yet"
    end
    | _ -> failwith "Case not implemented yet"
  with 
  | e ->
      let bt = Printexc.get_backtrace () in
      let err = Format.asprintf "BDep failed on instr: %a@.Exception thrown: %s@.BACKTRACE: %s@.@."
        (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst
        (Printexc.to_string e)
        bt in 
      raise @@ CircError err

let instrs_equiv
   (hyps       : hyps         )
   ((mem, mt)  : memenv       )
  ?(pstate     : _ = Map.empty)
   (s1         : instr list   )
   (s2         : instr list   ) : bool
=
  let env = LDecl.toenv hyps in

  let rd, rglobs = EcPV.PV.elements (EcPV.is_read  env (s1 @ s2)) in
  let wr, wglobs = EcPV.PV.elements (EcPV.is_write env (s1 @ s2)) in

  if not (List.is_empty rglobs && List.is_empty wglobs) then
    raise (CircError "the statements should not read/write globs");

  if not (List.for_all (EcTypes.is_loc |- fst) (rd @ wr)) then
    raise (CircError "the statements should not read/write global variables");

  let pstate = List.map (fun (pv, ty) -> { v_name = EcTypes.get_loc pv; v_type = ty; }) (rd @ wr) in
  let pstate, inputs = pstate_of_variables env pstate in

  let pstate1 = List.fold_left (process_instr hyps mem) pstate s1 in
  let pstate2 = List.fold_left (process_instr hyps mem) pstate s2 in

  Map.keys pstate |> Enum.for_all (fun var -> 
    let circ1 = Map.find var pstate1 in
    let circ1 = { circ1 with inps = inputs @ circ1.inps } in
    let circ2 = Map.find var pstate2 in
    let circ2 = { circ2 with inps = inputs @ circ2.inps } in
    circ_equiv circ1 circ2 None
  )
