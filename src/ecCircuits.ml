(* -------------------------------------------------------------------- *)
open EcUtils
open EcBigInt
open EcSymbols
open EcPath
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
  include Lospecs.Circuit_spec
end

module HL = struct
  include Lospecs.Hlaig
end

(* List of size n*w into list of n lists of size w *)
let rec blocks (xs: 'a list) (w: int) : 'a list list =
  match xs with
  | [] -> []
  | _ -> let h, t = List.takedrop w xs in
    h::(blocks t w)


(* -------------------------------------------------------------------- *)
type width = int
(* type deps = ((int * int) * int C.VarRange.t) list *)
(* Inputs to circuit functions: 
   Either bitstring of fixed size
   Or Array of fixed number of elements each of a fixed size *)
type cinput = 
  (* Name of input + size *)
  | BWInput of (ident * int)
  (* Name of array + array size + element size *)
  | BWAInput of (ident * int * int)

let cinput_to_string = function
  | BWInput (idn, w) -> Format.sprintf "(%s, %d)" (name idn) w
  | BWAInput (idn, n, w) -> Format.sprintf "(%s, %d@%d)" (name idn) n w

(* Checks whether inputs are the same up to renaming *)
let cinput_equiv (a: cinput) (b: cinput) : bool =
  match a, b with
  | BWInput (_, w), BWInput (_, w_) -> w = w_ 
  | BWAInput (_, n, w), BWAInput (_, n_, w_) -> n = n_ && w = w_ 
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
  | BWAInput (idn, n, w) -> (idn, n, w)
  | _ -> assert false

let bwinput_of_size (w : width) : cinput =
  let name = "bw_input" in
  BWInput (create name, w)

let bwainput_of_size (n : width) (w : width) : cinput =
  let name = "arr_input" in
  BWAInput (create name, n, w)

(* # of total bits of input *)
let size_of_cinput = function
  | BWInput (_, w) -> w
  | BWAInput (_, n, w) -> n*w

(* name of input *)
let ident_of_cinput = function
  | BWInput (idn, _) -> idn
  | BWAInput (idn, _, _) -> idn

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
  | BWArray a -> Format.sprintf "BWArray[%d@%d]" (Array.length a) (a.(0) |> List.length)

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
  | BWAInput (idn, n, w) -> 
    let c = C.reg ~name:(tag idn) ~size:(n*w) in
    let c = Array.of_list (blocks c w) in
    { circ = BWArray c; inps=[input]}

(* Packs a collection (list) of bitwords into an array *)
(* FIXME: maybe enforce that we want the array to be homogeneous? *)
let circ_array_of_bws (inps: cinput list) : circuit = 
  let rs = List.map circ_ident inps |> List.map (fun c -> destr_bwcirc c.circ) in
  {circ=BWArray (Array.of_list rs); inps}


(* Splits a bitword input into an array of chunks of size w *)
let circ_array_of_bw (inp: cinput) (w: width) : circuit =
  let r = circ_ident inp in
  let r = destr_bwcirc r.circ in
  {circ = BWArray(blocks r w |> Array.of_list); inps=[inp]}

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
  | BWInput (_, w), BWCirc r -> List.compare_length_with r w = 0
  | BWAInput (_, n, w), BWArray a -> (Array.length a = n) 
    && (Array.for_all (fun v -> List.compare_length_with v w = 0) a)
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
    Format.eprintf "Error applying on %s@." (circuit_to_string f);
    Format.eprintf "Arguments: @.";
    List.iter (Format.eprintf "%s@.") (List.map circ_to_string args);
    raise e
  in
  let args = List.combine f.inps args in
  let map_ = fun (id, i) ->
    let vr = List.find_opt (function 
      | BWInput (idn, _), _ when id = tag idn -> true
      | BWAInput (idn, _, _), _ when id = tag idn -> true
      | _ -> false 
      ) args
    in Option.bind vr 
      (function 
      | BWInput (_, w), BWCirc r -> List.at_opt r i
      | BWAInput (_, n, w), BWArray a -> 
        let ia, iw = (i / w), (i mod w) in
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
  | BWAInput (idn, n, w) -> BWAInput (fresh idn, n, w)

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
  | Some (n, t) -> BWAInput (idn, n, width_of_type env t)

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
let circuit_bwarray_set (n: width) (w: width) (i: int) : circuit =
  assert (n > i);
  let arr_inp = BWAInput (create "arr_input", n, w) in
  let bw_inp = BWInput (create "bw_input", w) in
  let arr = circ_ident arr_inp in
  let bw = circ_ident bw_inp in
  let () = (destr_bwarray arr.circ).(i) <- (destr_bwcirc bw.circ) in
  {circ= arr.circ; inps = [arr_inp; bw_inp]}

(* Same as above *)
let circuit_bwarray_get (n: width) (w: width) (i: int) : circuit =
  assert (n > i);
  let arr_inp = BWAInput (create "arr_input", n, w) in
  let arr = circ_ident arr_inp in
  {circ=BWCirc (destr_bwarray arr.circ).(i); inps=[arr_inp]}

  
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
    {circ=BWCirc(Array.fold_left (@) [] a); inps=c.inps}

(* Chunks a bitstring into an array of bitstrings, each of size w *)
let circuit_bw_split (c: circuit) (w: int) : circuit = 
  match c.circ with
  | BWArray _ -> assert false
  | BWCirc r -> 
    let nk = List.length r in
    assert (nk mod w = 0);
    let rs = blocks r w |> Array.of_list in
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
    | _, BWAInput (_, n, w)::cs -> let r1, r2 = List.takedrop (w*n) r in
      let r1 = blocks r1 w |> Array.of_list in
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

(* To be removed when we have external op bindings *)
let circuit_array_sliceget (w: width) (n: width) (m: width) (i: int) : circuit = 
  assert (n >= m*(i+1));
  (* assert (n mod m = 0); *)
  let arr_inp = bwainput_of_size n w in
  let arr = circ_ident arr_inp in
  let out = destr_bwarray arr.circ in
  let out = (Array.sub out (m*i) m) in
  {arr with circ = BWArray out}
  
(* To be removed when we have external op bindings *)
let circuit_array_sliceset (w: width) (n: width) (m: width) (i: int) : circuit = 
  assert (n >= m*(i + 1));
  (* assert (n mod m = 0); *)
  let arr_inp = bwainput_of_size n w in
  let new_arr_inp = bwainput_of_size m w in
  let arr = circ_ident arr_inp in
  let new_arr = circ_ident new_arr_inp in
  let arr_b = Array.to_list (destr_bwarray arr.circ) in
  let new_arr_b = Array.to_list (destr_bwarray new_arr.circ) in
  let out = List.take (m*i) arr_b @ new_arr_b @ List.drop (m*(i+1)) arr_b |> Array.of_list in
  {arr with circ = BWArray out; inps = [arr_inp; new_arr_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwarray_slice_get (n: width) (w: width) (aw: int) (i: int) : circuit =
  assert (n*w >= (i + 1)*aw);
  assert (n*w mod aw = 0);
  let arr_inp = bwainput_of_size n w in
  let arr = circ_ident arr_inp in
  let arr = circuit_flatten arr in
  {circ=BWCirc (List.drop (i*aw) (destr_bwcirc arr.circ) |> List.take aw); inps=[arr_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwarray_slice_set (n: width) (w: width) (aw: int) (i: int) : circuit =
  assert (n*w >= (i + 1)*aw);
  assert (n*w mod aw = 0);
  let bw_inp = bwinput_of_size aw in
  let bw = circ_ident bw_inp in
  let arr_inp = bwainput_of_size n w in
  let arr = circ_ident arr_inp in
  let arr = circuit_flatten arr in
  let arr_circ = destr_bwcirc arr.circ in
  let bw_circ = destr_bwcirc bw.circ in
  let res_circ = (List.take (i*aw) arr_circ) @ bw_circ @ (List.drop ((i+1)*aw) arr_circ) in
  let res_circs = blocks res_circ w in
  {circ=BWArray (Array.of_list res_circs); inps=[arr_inp; bw_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwcirc_get (w: width) (aw:int) (i: int) : circuit =
  assert (w > i*aw);
  assert (w mod aw = 0);
  let bw_inp = bwinput_of_size w in
  let bw = circ_ident bw_inp in
  let bw = destr_bwcirc bw.circ in
  {circ = BWCirc(List.take aw (List.drop (i*aw) bw)); inps=[bw_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwcirc_set (w: width) (aw:int) (i:int) : circuit =
  assert (w > i*aw);
  assert (w mod aw = 0);
  let bw_inp = bwinput_of_size w in
  let bw = circ_ident bw_inp in
  let bw = destr_bwcirc bw.circ in
  let bw2_inp = bwinput_of_size aw in
  let bw2 = circ_ident bw2_inp in
  let bw2 = destr_bwcirc bw2.circ in
  let bw = List.take (i*aw) bw @ bw2 @ List.drop ((i+1)*aw) bw in
  {circ = BWCirc bw; inps=[bw_inp; bw2_inp]}

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

(* Partitions into blocks of type n -> m *)
let circuit_mapreduce (c: circuit) (n:int) (m:int) : circuit list =
  let const_inp = BWInput (create "const", n) in
  let c = circuit_flatten c in
  let c = circuit_aggregate_inps c in
  let r = destr_bwcirc c.circ in
  let deps = HL.deps r in
  let deps = HL.split_deps m deps in
  assert (HL.block_list_indep deps);
  assert (List.for_all (HL.check_dep_width n) (List.snd deps));
  assert ((List.fold_left (+) 0 (List.map size_of_cinput c.inps)) mod n = 0);
  
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
  let cblocks = blocks cblocks w in 
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
  
  let is_baseop (env: env) (p: path) : bool = 
    match (EcPath.toqsymbol p) with
    (* | ["Top"; "JWord"; _], _ -> true *)
    (* | ["Top"; "JModel_x86"], _ -> true *)

    (* AdHoc for barrett FIXME: remove later *)
    | _, "sext16_32" -> true
    | _, "uext16_32" -> true
    | _, "sar_32_26" -> true
    | _, "truncate32_16" -> true
    | _, "truncate32_8" -> true
    | _, "eqmod64q" -> true
    | _, "bvueq" -> true
    | _, "bvseq" -> true
    | _, "=>" -> true
    | _, "<=>" -> true
    | _, "true" -> true
    | _, "false" -> true
    | _, "`>>`" -> true
    | _, "`|>>`" -> true
    | _, "`<<`" -> true
    | _, "[-]" -> true

    | _, "zeroextu64" -> true
    
    | _ -> begin match EcEnv.Circuit.lookup_bvoperator_path env p with
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
      | "W4u16" -> 16
      | "W16u16" -> 256
      | _ -> Format.eprintf "Unknown size for path %s@." (EcSymbols.string_of_qsymbol qpath); assert false
      in 

    begin match op with
    | "[-]" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc (C.opp c1); inps = [BWInput(id1, size)]}

    | "`>>`" -> (* FIXME: remove after getting truncate *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size:8 ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`R ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, 8)]}

    | "`|>>`" -> (* FIXME: get arithmetic shift from qfabv ops *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size:8 ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`R ~sign:`A c1 c2); inps = [BWInput(id1, size); BWInput(id2, 8)]}

    | "`<<`" -> (* FIXME: remove after getting truncate *)
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size:8 ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`L ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, 8)]}


    (* Comparisons: *)
    | "\\ule" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc([C.uge c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}
    | "\\ult" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc([C.ugt c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}
    (* Comparisons: *)
    | "\\sle" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc([C.sge c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}
    | "\\slt" -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc([C.sgt c2 c1]); inps=[BWInput(id1, size); BWInput(id2, size)]}
    
    (* Conversions 
      These int conversions assume a fixed size,
      FIXME: require all int conversions to be explicit
      (and have some upper bound somewhere of what is the maximum size )
    *)
    | "of_int" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(c1); inps = [BWInput(id1, 256)]} (* FIXME: Assumes integeres are 256 bits *)
    
    | "to_uint" ->
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.uextend ~size:256 c1); inps = [BWInput(id1, size)]} (* FIXME: Assumes integeres are 256 bits *)

    | "zeroextu64" ->
    assert(size <= 64);
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size ~name:id1.id_tag in
    {circ = BWCirc(C.uextend ~size:64 c1); inps = [BWInput(id1, size)]}

    
    | _ -> 
      let err = Format.asprintf "Unregistered JOp : %s @." (EcSymbols.string_of_qsymbol qpath) in
      raise @@ CircError err
    end
  (* AdHoc stuff for barrett example FIXME: remove later *)
  | _, "sext16_32" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    {circ = BWCirc(C.sextend ~size:32 c1); inps = [BWInput(id1, 16)]}

    | _, "uext16_32" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    {circ = BWCirc(C.uextend ~size:32 c1); inps = [BWInput(id1, 16)]}

  
  | _, "sar_32_26" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:32 ~name:id1.id_tag in
    {circ = BWCirc(C.arshift ~offset:26 c1); inps = [BWInput(id1, 32)]}

  | _, "truncate32_16" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    { circ = BWCirc(c1); inps=[BWInput(id1, 32)]}

  | _, "truncate32_8" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:8 ~name:id1.id_tag in
    { circ = BWCirc(c1); inps=[BWInput(id1, 32)]}

  
  | _, "bvueq" -> (* FIXME: add general parsing for equality *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:16 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:16 ~name:id2.id_tag in
    {circ = BWCirc([C.bvueq c1 c2]); inps = [BWInput(id1, 16); BWInput(id2, 16)]}
  
  | _, "bvseq" -> (* FIXME: remove hardcoded size *)
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:32 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:32 ~name:id2.id_tag in
    {circ = BWCirc([C.bvseq c1 c2]); inps = [BWInput(id1, 32); BWInput(id2, 32)]}

  | _, "=>" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = BWCirc(C.lor_ (C.lnot_ c1) c2); inps = [BWInput(id1, 1); BWInput(id2, 1)]}
  
  | _, "<=>" ->
    let id1 = EcIdent.create temp_symbol in
    let c1 = C.reg ~size:1 ~name:id1.id_tag in
    let id2 = EcIdent.create temp_symbol in
    let c2 = C.reg ~size:1 ~name:id2.id_tag in
    {circ = BWCirc(C.lxnor_ c1 c2); inps = [BWInput(id1, 1); BWInput(id2, 1)]}
    
  | _, "true" ->
    {circ = BWCirc([C.true_]); inps = []}

  | _, "false" ->
    {circ = BWCirc([C.false_]); inps = []}

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
    {circ = BWCirc([dc]); inps = [BWInput(id1, 16); BWInput(id2, 16)]}
  
  | _ -> begin match EcEnv.Circuit.lookup_bvoperator_path env p with
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

    | Some { kind = `UDiv size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.udiv c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `URem size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.urem c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Shl  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`L ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Shr  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.shift ~side:`R ~sign:`L c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

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

    | _ -> raise @@ CircError "Failed to generate op"
    end
end

module ArrayOps = struct
  let temp_symbol = "temp_array_input"

  let is_arrayop (env: env) (pth: path) : bool =
    Option.is_some
      (EcEnv.Circuit.reverse_array_operator env pth)
  
  let destr_getset_opt (env: env) (pth: path) : crb_array_operator option =
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

(* TODO: simplify args and unify dealing with cache / vars *)
let circuit_of_form 
  ?(pstate : pstate = Map.empty) 
  ?(cache  : cache = Map.empty) 
   (env    : env) 
   (f      : EcAst.form) 
  : circuit =
  
  let rec doit (cache: (ident, (cinput * circuit)) Map.t) (env: env) (f: form) : env * circuit = 
    let process_bwslice_ops (cache: _) (env: env) (f: form) : (env * circuit) option =
      let (fp, _), fs = destr_op_app f in
      match (String.split_on_char '_' @@ snd (EcPath.toqsymbol fp)) with
      | ["sliceget"; aw; n; w] ->
        let aw, n, w = (String.to_int aw, String.to_int n, String.to_int w) in
        let arr, i = match fs with
        | [arr; {f_node= Fint i; _}] -> arr, (BI.to_int i)
        | _ -> assert false
        in
        let r = circuit_bwarray_slice_get n w aw i in
        let env, arr = doit cache env arr in
        Some (env, compose r [arr])
      | ["sliceget"; aw; w] ->
        let aw, w = (String.to_int aw, String.to_int w) in
        let bw, i = match fs with
        | [bw; {f_node=(Fint i)}] -> bw, (BI.to_int i)
        | _ -> assert false
        in
        assert(w = width_of_type env bw.f_ty);
        assert(aw = width_of_type env f.f_ty);
        let env, bw = doit cache env bw in
        let get_circ = circuit_bwcirc_get w aw i in
        Some (env, compose get_circ [bw])
      | ["sliceset"; aw; n; w] ->
        let aw, n, w = (String.to_int aw, String.to_int n, String.to_int w) in 
        let arr, i, v = match fs with
        | [arr; {f_node= Fint i; _}; v] -> arr, (BI.to_int i), v
        | _ -> assert false
        in
        let r = circuit_bwarray_slice_set n w aw i in
        let env, arr = doit cache env arr in
        let env, v = doit cache env v in
        Some (env, compose r [arr; v])
      | ["sliceset"; aw; w] ->
        let aw, w = (String.to_int aw, String.to_int w) in 
        let bw, i, v = match fs with
        | [bw; {f_node=(Fint i)}; v] -> bw, (BI.to_int i), v
        | _ -> assert false
        in
        assert(w = width_of_type env bw.f_ty);
        assert(aw = width_of_type env f.f_ty);
        assert(aw = width_of_type env v.f_ty);
        let env, bw = doit cache env bw in
        let env, v = doit cache env v in
        let set_circ = circuit_bwcirc_set w aw i in
        Some (env, compose set_circ [bw; v])
      | ["asliceget"; bw; n; m] ->
        let bw, n, m = (String.to_int bw, String.to_int n, String.to_int m) in
        let arr, i = match fs with
        | [arr; {f_node= Fint i; _}] -> arr, (BI.to_int i)
        | _ -> assert false
        in
        let r = circuit_array_sliceget bw n m i in
        let env, arr = doit cache env arr in
        Some (env, compose r [arr])
      | ["asliceset"; bw; n; m] ->
        let bw, n, m = (String.to_int bw, String.to_int n, String.to_int m) in 
        let arr, i, v = match fs with
        | [arr; {f_node= Fint i; _}; v] -> arr, (BI.to_int i), v
        | _ -> assert false
        in
        let r = circuit_array_sliceset bw n m i in
        let env, arr = doit cache env arr in
        let env, v = doit cache env v in
        Some (env, compose r [arr; v])
      | "sliceget"::xs -> assert false
      | "sliceset"::xs -> assert false
      | "asliceget"::xs -> assert false
      | "asliceset"::xs -> assert false
      | _ -> None
    in

    let process_bw_oflist (cache: _) (env: env) (f: form) : (env * circuit) option =
      let (pth, _), fs = destr_op_app f in
      match (EcPath.toqsymbol pth), fs with
      | (_, "of_list"), [wtn; vs] ->
        let _, n, w = destr_bwainput @@ cinput_of_type env f.f_ty in
        (* FIXME: have an actual way to get sizes without creating new idents *)
        let vs = EcCoreFol.destr_list vs in
        let env, vs = List.fold_left_map (doit cache) env vs in
        begin match EcCoreFol.is_witness wtn with
        | false -> 
          let env, wtn = doit cache env wtn in
          assert(List.is_empty wtn.inps && List.for_all (fun c -> List.is_empty c.inps) vs);
          let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
          let wtn = destr_bwcirc wtn.circ in
          let r = Array.init n (fun i -> List.nth_opt vs i |> Option.default wtn) in
          Some(env, {circ = BWArray r; inps = []})
        | true -> 
          assert (List.compare_length_with vs n = 0);
          assert (List.for_all (fun c -> List.is_empty c.inps) vs);
          let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
          let r = Array.of_list vs in
          Some(env, {circ=BWArray r; inps=[]})
        end
      | _ -> 
        (* Format.eprintf "Not oflist %s@." (EcPath.tostring pth); *) 
        None
    in
        
    
    match f.f_node with
    (* hardcoding size for now FIXME *)
    | Fint z -> env, {circ = BWCirc(C.of_bigint ~size:256 (to_zt z)); inps = []}
      (* failwith "Add logic to deal with ints (maybe force conversion?)" *)
      (* hlenv, C.of_bigint ~size:256 (EcAst.BI.to_zt z) *)
    | Fif (c_f, t_f, f_f) -> 
        let env, c_c = doit cache env c_f in
        let env, t_c = doit cache env t_f in
        let env, f_c = doit cache env f_f in
        let () = assert (List.length (destr_bwcirc c_c.circ) = 1) in
        let () = assert (List.is_empty c_c.inps) in
        let () = assert (List.is_empty t_c.inps) in
        let () = assert (List.is_empty f_c.inps) in
        let c_c = List.hd (destr_bwcirc c_c.circ) in
        begin
        match t_c.circ, f_c.circ with
        | BWCirc t_c, BWCirc f_c ->
        env, {
          circ = BWCirc (C.ite c_c t_c f_c);
          inps = []; 
        }
        | BWArray t_cs, BWArray f_cs when (Array.length t_cs = Array.length f_cs) ->
          env, {
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
        if (cinput_equiv inp (cinput_of_type env f.f_ty)) then
        env, circ
        else 
          let err = Format.asprintf "Var binding shape %s for %s does not match shape of form type %s@."
           (cinput_to_string inp) idn.id_symb (cinput_of_type env f.f_ty |> cinput_to_string) in
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
      (* else if ArrayOps.is_arrayop env pth then *)
        (* let circ = ArrayOps.circuit_of_arrayop env pth in *)
        (* op_cache := Mp.add pth circ !op_cache; *)
        (* env, circ *)
      else
        let f = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper ( Some (OP_Plain f)) -> f
        | _ -> Format.eprintf "%s@." (EcPath.tostring pth); failwith "Unsupported op kind"
        in 
        let env, circ = doit cache env f in
        op_cache := Mp.add pth circ !op_cache;
        env, circ
    end
    | Fapp _ -> 
      let t1 = process_bwslice_ops cache env f in
      let t1 = match t1 with
        | Some (env, c) -> t1
        | None -> process_bw_oflist cache env f 
      in
      begin match t1 with
        | Some (env, c) -> env, c
        | None ->
        let (f, fs) = EcCoreFol.destr_app f in
        let env, res = match ArrayOps.destr_getset_opt env @@ (EcCoreFol.destr_op f |> fst) with
            (* Assuming correct types coming from EC *)
            (* FIXME: add typechecking here ? *)
          | Some ({ size = n }, `Get) -> let env, res = 
            match fs with
            | [arr; {f_node=Fint i; _}] ->
              let (_, t) = destr_array_type env arr.f_ty |> Option.get in
              let w = width_of_type env t in
              let env, arr = doit cache env arr in
              env, compose (circuit_bwarray_get n w (BI.to_int i)) [arr]
            | _ -> raise (CircError "set")
            in env, res
          | Some({ size = n }, `Set) -> let env, res = 
            match fs with
            | [arr; {f_node=Fint i; _}; v] ->
              let w = width_of_type env v.f_ty  in
              let env, arr = doit cache env arr in
              let env, v = doit cache env v in
              env, compose (circuit_bwarray_set n w (BI.to_int i)) [arr; v]
            | _ -> raise (CircError "set")
            in env, res
          | _ -> 
            let env, f_c = doit cache env f in
            let env, fcs = List.fold_left_map
              (doit cache)
              env fs 
            in
            env, compose f_c fcs
          in env, res
      end
      
    | Fquant (qnt, binds, f) -> 
      (* FIXME: check if this is desired behaviour for exists and add logic for others *)
      let binds = List.map (fun (idn, t) -> cinput_of_type ~idn env (gty_as_ty t)) binds in
      let cache = List.fold_left 
        (fun cache inp -> 
          let circ = {(circ_ident inp) with inps = []} in
          Map.add (ident_of_cinput inp) (inp, circ) cache) cache binds in
      let env, circ = doit cache env f in
      begin match qnt with
      | Llambda -> env, {circ with inps=binds @ circ.inps} (* FIXME: check input order *)
      | Lforall 
      | Lexists -> assert false
      (* TODO: figure out how to handle quantifiers *)
      end
    | Fproj (f, i) ->
        begin match f.f_node with
        | Ftuple tp ->
          doit cache env (tp |> List.drop (i-1) |> List.hd)
        | _ -> failwith "Don't handle projections on non-tuples"
        end
    | Fmatch  (f, fs, ty) -> assert false
    | Flet    (lpat, v, f) -> 
      begin match lpat with
      | LSymbol (idn, ty) -> 
        let env, vc = doit cache env v in
        let inp = cinput_of_type ~idn env ty in
        let () = assert (match_arg inp vc.circ) in
        let cache = Map.add idn (inp, vc) cache in
        doit cache env f
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
        | None -> let circ = circ_ident (cinput_of_type ~idn:(create "uninit") env f.f_ty) in
          {circ with inps=[]}
      (* EXPERIMENTAL: allowing unitialized values *)
          (* failwith ("No value for var " ^ v) *)
      in env, res
    | Fglob   (id, mem) -> assert false
    | Ftuple  comps -> assert false
    | _ -> failwith "Not yet implemented"

  in 
  let env, f_c = doit cache env f in
  f_c


let circuit_of_path (env: env) (p: path) : circuit =
  let f = EcEnv.Op.by_path p env in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> failwith "Invalid operator type"
  in
  circuit_of_form env f

let input_of_variable (env:env) (v: variable) : circuit * cinput =
  let idn = create v.v_name in
  let inp = cinput_of_type ~idn env v.v_type in
  {(circ_ident inp) with inps=[]}, inp
  

let pstate_of_memtype ?(pstate = Map.empty) (env: env) (mt: memtype) =
  let invs = match mt with
  | Lmt_concrete (Some lmt) -> lmt.lmt_decl 
    |> List.filter_map (fun ov -> if Option.is_none ov.ov_name then None
                                  else Some {v_name = Option.get ov.ov_name; v_type=ov.ov_type})
  | _ -> assert false
  in

  let inps = List.map (input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) invs in
  let pstate = List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 
  in pstate, inps


let process_instr (env:env) (mem: memory) ?(cache: cache = Map.empty) (pstate: _) (inst: instr) =
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
  let pstate, inps = pstate_of_memtype ~pstate env mt in
  let pstate_left = List.fold_left (process_instr env mem) pstate insts_left in
  let pstate_right = List.fold_left (process_instr env mem) pstate insts_right in

  (* if (Map.keys pstate_left |> Set.of_enum) != (Map.keys pstate_right |> Set.of_enum) then *)
    (* begin *)
    (* Format.eprintf "Left: @."; *)
    (* Map.iter (fun k _ -> Format.eprintf "%s@." k) pstate_left; *)
    (* Format.eprintf "Right: @."; *)
    (* Map.iter (fun k _ -> Format.eprintf "%s@." k) pstate_right; *)
    (* false *)
    (* end *)
  (* else *)
    Map.foldi (fun var circ bacc -> 
      let circ = {circ with inps=inps @ circ.inps} in
      let circ2 = (Map.find var pstate_right) in
      let circ2 = {circ2 with inps=inps @ circ2.inps} in
      bacc && (circ_equiv circ circ2 None)) 
    pstate_left true