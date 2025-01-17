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
open EcCoreGoal

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

type asize = { wordsize: int; nelements: width; }

type tpsize = { wordsizes : int list; npos : width; }

let size_of_asize (sz : asize) : int =
  sz.wordsize * sz.nelements

let size_of_tpsize (sz : tpsize) : int =
  List.sum sz.wordsizes

exception CircError of string

(* type deps = ((int * int) * int C.VarRange.t) list *)
(* Inputs to circuit functions: 
   Either bitstring of fixed size
   Or Array of fixed number of elements each of a fixed size *)
type cinput = 
  (* Name of input + size *)
  | BWInput of (ident * int)
  (* Name of array + (array size x element size) *)
  | BWAInput of (ident * asize)
  (* Name of tuple, + (tuple size x element size) *)
  | BWTInput of (ident * tpsize)

let asize_to_string (asize : asize) : string =
  Format.sprintf "%d[%d]" asize.wordsize asize.nelements

let tpsize_to_string (tpsize : tpsize) : string =
  match tpsize.wordsizes with
  | [] -> "()"
  | sz::szs ->
    Format.asprintf "(%d%a)" sz (fun fmt szs -> List.iter (Format.fprintf fmt ", %d") szs) szs  

let cinput_to_string = function
  | BWInput (idn, w) -> Format.sprintf "(%s(id=%d), %d)" (name idn) (tag idn) w
  | BWAInput (idn, sz) -> Format.sprintf "(%s(id=%d), %s)" (name idn) (tag idn) (asize_to_string sz)
  | BWTInput (idn, sz) -> Format.sprintf "(%s(id=%d), %s)" (name idn) (tag idn) (tpsize_to_string sz)

(* Checks whether inputs are the same up to renaming *)
let cinput_equiv (a: cinput) (b: cinput) : bool =
  match a, b with
  | BWInput (_, w1), BWInput (_, w2) -> w1 = w2 
  | BWAInput (_, sz1), BWAInput (_, sz2) -> sz1 = sz2 
  | BWTInput (_, sz1), BWTInput (_, sz2) -> 
    sz1.npos = sz2.npos && 
    (List.for_all2 (=) sz1.wordsizes sz2.wordsizes)
  | _ -> false

let is_bwinput = function
  | BWInput _ -> true
  | _ -> false

let is_bwainput = function
  | BWAInput _ -> true
  | _ -> false

let destr_bwinput = function
  | BWInput (idn, w) -> (idn, w)
  | _ -> raise (CircError "destr_bwinput")

let destr_bwainput = function
  | BWAInput (idn, sz) -> (idn, sz)
  | _ -> raise (CircError "destr_bwainput")

let destr_tpinput = function
  | BWTInput (idn, sz) -> (idn, sz)
  | _ -> raise (CircError "destr_tpinput")

let bwinput_of_size (w : width) : cinput =
  let name = "bw_input" in
  BWInput (create name, w)

let bwainput_of_size ~(nelements : width) ~(wordsize : width) : cinput =
  let name = "arr_input" in
  BWAInput (create name, { nelements; wordsize; })

let bwtpinput_of_sizes ~(npos : width) ~(wordsizes : int list) : cinput =
  let name = "tp_input" in
  BWTInput (create name, { npos; wordsizes; })

(* # of total bits of input *)
let size_of_cinput = function
  | BWInput (_, w) -> w
  | BWAInput (_, sz) -> size_of_asize sz
  | BWTInput (_, sz) -> size_of_tpsize sz

(* name of input *)
let ident_of_cinput = function
  | BWInput (idn, _) -> idn
  | BWAInput (idn, _) -> idn
  | BWTInput (idn, _) -> idn

(* Base circuit, represents body of a circuit function *)
(* BWArray is homogeneous, BWTuple it not *)
type circ = 
  | BWCirc of C.reg
  | BWArray of C.reg array
  | BWTuple of C.reg list

let is_bwcirc = function
  | BWCirc _ -> true
  | _ -> false

let is_bwarray = function
  | BWArray _ -> true
  | _ -> false

let is_bwtuple = function
  | BWTuple _ -> true
  | _ -> false

let destr_bwcirc = function
  | BWCirc r -> r
  | _ -> raise (CircError "destr_bwcirc")

let destr_bwarray = function
  | BWArray a -> a
  | _ -> raise (CircError "destr_bwarray")

let destr_bwtuple = function
  | BWTuple tp -> tp
  | _ -> raise (CircError "destr_bwtuple")

(* # of total bits of output *)
let size_of_circ = function
  | BWCirc r -> List.length r
  | BWArray a -> if Array.length a = 0 then 0 else
    (Array.length a) * (List.length a.(0))
  | BWTuple tp -> List.fold_left (+) 0 (List.map List.length tp)

(* Simple representation *)
let circ_to_string = function 
  | BWCirc r -> Format.sprintf "BWCirc@%d" (List.length r)
  | BWArray a -> Format.sprintf "BWArray[%d[%d]]" (a.(0) |> List.length) (Array.length a)
  | BWTuple tp -> Format.asprintf "BWTuple(%a)" 
    (fun fmt rs -> if List.is_empty rs then () 
      else Format.fprintf fmt "%d" (List.hd rs); List.iter (Format.fprintf fmt ", %d") (List.tl rs)) 
    (List.map (List.length) tp)

let circ_of_int (size: int) (z: zint) : circ =
  BWCirc (C.of_bigint_all ~size (to_zt z))

let circ_array_of_ints (size: int) (zs: zint list) : circ = 
  let cs = List.map (fun z -> C.of_bigint_all ~size (to_zt z)) zs in
  BWArray (Array.of_list cs)

let circ_tuple_of_ints (size: int) (zs: zint list) : circ =
  let cs = List.map (fun z -> C.of_bigint_all ~size (to_zt z)) zs in
  BWTuple cs
  

(* Checks whether the output shapes are the same *)
let circ_shape_equal (c1: circ) (c2: circ) = 
  match c1, c2 with
  | BWArray r1, BWArray r2 -> 
    Array.length r1 = Array.length r2 && 
    (Array.length r1 = 0 || List.length r1.(0) = List.length r2.(0))
  | BWCirc r1, BWCirc r2 -> List.compare_lengths r1 r2 = 0
  | BWTuple tp1, BWTuple tp2 -> List.compare_lengths tp1 tp2 = 0 && List.for_all2 (fun a b -> List.compare_lengths a b = 0) tp1 tp2
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
    let out = Array.init sz.nelements (fun ja ->
      List.init sz.wordsize (fun j -> C.input (idn.id_tag, ja*sz.wordsize + j))) 
    in
    { circ = BWArray out; inps=[input]}
  | BWTInput (idn, sz) ->
    let out = List.fold_left_map 
      (fun acc sz -> acc + sz, List.init sz (fun j -> C.input (idn.id_tag, acc + j))) 
      0
      sz.wordsizes
      |> snd
    in
    {circ = BWTuple out; inps=[input]}


(* Checks whether the two circuits have the same inputs up to renaming *)
let input_shape_equal (f: circuit) (g: circuit) : bool = 
  (List.compare_lengths f.inps g.inps = 0) && 
  (List.for_all2 (cinput_equiv) (f.inps) (g.inps))

(* Checks if there are no shared inputs among elements of the list
  That is, the name of each input to each circuit in the list does not 
  appear as an input in another element in the list *)
(* FIXME: maybe remove ? *)
(*let inputs_indep (fs: circuit list) : bool =*)
(*  let s = List.map (fun c -> Set.of_list (List.map ident_of_cinput c.inps)) fs in*)
(*  let c = List.fold_left (fun acc s -> acc + (Set.cardinal s)) 0 s in*)
(*  let s = List.fold_left Set.union Set.empty s in*)
(*  (Set.cardinal s) = c*)

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
  | BWTInput (_, sz), BWTuple tp
    when List.compare_length_with tp sz.npos = 0
      && List.for_all2 (fun v1 v2 -> List.compare_length_with v1 v2 = 0) tp sz.wordsizes ->
      true
  | _ -> Format.eprintf "inp: %s does not match %s@."
    (cinput_to_string inp) (circ_to_string val_); false

(* 
   Fully applies a function to a list of constant arguments
   returning a constant value
   THROWS: CircError on failure, should always be caught
*) 
let apply (f: circuit) (args: circ list) : circ = 
  let () = try
    assert (List.compare_lengths f.inps args = 0);
    assert (List.for_all2 match_arg f.inps args);
  with Assert_failure _ as _e -> 
    let err = Format.asprintf 
      "Backtrace: %s@.\
       Error applying on %s@.\
       Arguments: @.%a@." (Printexc.get_backtrace ())
    (circuit_to_string f)
    (fun fmt args -> List.iter (Format.fprintf fmt "%s@.") args) (List.map circ_to_string args) in
    raise (CircError err)
  in
  let args = List.combine f.inps args in
  let map_ = fun (id, i) ->
    let vr = List.find_opt (function 
      | BWInput (idn, _), _ when id = tag idn -> true
      | BWAInput (idn, _), _ when id = tag idn -> true
      | BWTInput (idn, _), _ when id = tag idn -> true
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
      | BWTInput (_, sz), BWTuple tp ->
        let tp = List.flatten tp in
        (List.at_opt tp i) 
      | _ -> 
        let err = Format.asprintf "Backtrace: %s@.\
          Error applying on %s@.\
          Arguments: @.%a@.\
          Mismatch between argument types.@." 
          (Printexc.get_backtrace ())
          (circuit_to_string f)
          (fun fmt args -> List.iter (Format.fprintf fmt "%s@.") args) 
          (List.map circ_to_string (List.snd args)) 
        in raise (CircError err)
        )
  in
  match f.circ with
  | BWCirc r -> BWCirc (C.maps map_ r)
  | BWArray rs -> BWArray (Array.map (C.maps map_) rs)
  | BWTuple tp -> BWTuple (List.map (C.maps map_) tp)

(* Given an input returns a new input with the same shape *)
let fresh_cinput (c: cinput) : cinput = 
  match c with
  | BWInput (idn, w) -> BWInput (fresh idn, w)
  | BWAInput (idn, sz) -> BWAInput (fresh idn, sz)
  | BWTInput (idn, sz) -> BWTInput (fresh idn, sz)

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

let rec merge_inputs (c: cinput list) (d: cinput list) : cinput list =
  match c, d with
  | [], [] -> []
  | xs, []
  | [], xs -> xs
  | x::xs, y::ys -> if x = y then x::(merge_inputs xs ys) else
    c @ d

(* -------------------------------------------------------------------- *)

let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({size=size_arr}, {size=size_bs}) -> size_arr * size_bs
  | _ -> match EcEnv.Circuit.lookup_bitstring_size env t with
    | Some w -> w
    | None -> let err = Format.asprintf "No bitvector binding for type %a@."
    (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in 
    raise (CircError err)

(* returns size of array and underlying element type if array type, otherwise None *)
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

(* Given an EC type with the correct bindings returns a circuit input
   matching the shape of that type *)
let cinput_of_type ?(idn: ident option) (env: env) (t: ty) : cinput = 
  let name = "from_type" in
  let idn = match idn with
  | Some idn -> idn
  | None -> create name 
  in
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | None -> BWInput (idn, width_of_type env t)
  | Some ({size=nelements}, {size=wordsize}) ->
    BWAInput (idn, { nelements; wordsize })

(* given f(inps1), g(inps2) returns h(inps1,inps2) = f(a) @ g(b)
   where @ denotes concatenation of circuits *)
let circuit_concat (c: circuit) (d: circuit) : circuit =
    match c.circ, d.circ with
    | BWCirc ccirc, BWCirc dcirc -> 
      {circ=BWCirc(ccirc @ dcirc); inps=merge_inputs c.inps d.inps}
    | _ -> raise (CircError "concat")

(* Same as above but concatenates arrays of bitwords *)
let circuit_array_concat (c: circuit) (d: circuit) : circuit =
  match c.circ, d.circ with
  | BWArray carr, BWArray darr -> 
    {circ=BWArray(Array.concat [carr; darr]); inps=merge_inputs c.inps d.inps}
  | _ -> raise (CircError "array concat")

let (++) : circuit -> circuit -> circuit = circuit_concat
let (+@) : circuit -> circuit -> circuit = circuit_array_concat

(* Given f_i(inps_i) returns h(inps_1, ...) = f_1(inps_1) @ ... 
  aka given a list of functions returns a function that concatenates 
  their outputs, given all their inputs *)
let rec circuit_aggregate (c: circuit list) : circuit =
  match c with
  | [] -> assert false
  | c :: [] -> c
  | d :: c :: [] -> d ++ c
  | c :: cs -> c ++ (circuit_aggregate cs)

let rec circuit_array_aggregate (c: circuit list) : circuit =
  match c with
  | [] -> assert false
  | c :: [] -> c
  | d :: c :: [] -> d +@ c
  | c :: cs -> c +@ (circuit_array_aggregate cs)

let circuit_bwarray_set ~(nelements : width) ~(wordsize : width) (i: int) : circuit =
  (* Index guarantee should come from EC *)
  (* assert (nelements > i); *)
  let arr_inp = BWAInput (create "arr_input", { nelements; wordsize; }) in
  let bw_inp = BWInput (create "bw_input", wordsize) in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let bw_id = (ident_of_cinput bw_inp).id_tag in
  let out = Array.init nelements (fun ja ->
    if ja = i then List.init wordsize (fun j -> C.input (bw_id, j))
    else List.init wordsize (fun j -> C.input (arr_id, ja*wordsize + j))) in
  {circ= BWArray (out); inps = [arr_inp; bw_inp]}

let circuit_bwarray_get ~(nelements : width) ~(wordsize : width) (i: int) : circuit =
  (* assert (nelements > i); *)
  let arr_inp = BWAInput (create "arr_input", { nelements; wordsize; }) in
  let out = List.init wordsize (fun j -> C.input ((ident_of_cinput arr_inp).id_tag, j + wordsize*i)) in
  {circ=BWCirc (out); inps=[arr_inp]}
  
(* Function composition for circuits *)
(* Reduces to application if arguments are 0-ary *)
(*
  THROWS: CircError on failure (from apply calls)
*)
let compose (f: circuit) (args: circuit list) : circuit = 
  try 
    {circ=apply f (List.map (fun c -> c.circ) args); 
    inps=List.fold_right (@) (List.map (fun c -> c.inps) args) []} 
  with CircError err ->
    raise (CircError ("On compose call, apply failed with err:\n" ^ err) )

let compute ~(sign:bool) (f: circuit) (r: BI.zint list) : BI.zint = 
  (* FIXME: can we remove the parenthesis around the try/with block? *)
  (try
    assert (List.compare_lengths f.inps r = 0)
  with Assert_failure _ -> 
    let err = Format.asprintf 
    "Wrong # of arguments (%d provided, %d expected) for compute"
    (List.length r)
    (List.length f.inps)
    in 
    raise (CircError err));
  let vs = List.map2 (fun inp r -> 
    let _, size = destr_bwinput inp in
    BWCirc(C.of_bigint_all ~size (BI.to_zt r))
  ) f.inps r in
  let res = apply f vs in
  let res = destr_bwcirc res in 
  let res = List.map (function | {C.gate = C.False; C.id = id} -> 
    if id >= 0 then false
    else true
    | _ -> raise (CircError "Non-constant result in compute (not fully applied?)")
  ) res in
  (* conversion functions need to be reworked FIXME *)
  if sign then 
  C.sbigint_of_bools res |> BI.of_zt
  else
  C.ubigint_of_bools res |> BI.of_zt

(* 
  Unifies inputs to allow for equivalence testing 
*)
let unify_inputs (fs: circuit list) : circuit list option =
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
  | BWTuple tp ->
    List.map (fun r -> {circ=BWCirc r; inps=c.inps}) tp

(* Ident on bitstrings, flattens arrays into bitstrings *)
let circuit_flatten (c: circuit) : circuit =
  match c.circ with
  | BWCirc _ -> c
  | BWArray a -> 
    {circ=BWCirc(Array.fold_right (@) a []); inps=c.inps}
  | BWTuple _ -> raise (CircError "Cannot flatten tuple")

(* Chunks a bitstring into an array of bitstrings, each of size w *)
let circuit_bw_split (c: circuit) (w: int) : circuit = 
  match c.circ with
  | BWArray _ -> raise (CircError "Cannot chunk array")
  | BWTuple _ -> raise (CircError "Cannot chunk tuple")
  | BWCirc r -> 
    let nk = List.length r in
    if (nk mod w = 0) then
      let rs = List.chunkify w r |> Array.of_list in
      {circ=BWArray rs; inps = c.inps}
    else
      let err = Format.asprintf "Size of circ (%d) not evenly divided by chunk size (%d)" nk w in
      raise (CircError err)

(* Zero-extends a bitstring *)
let circuit_bw_zeroextend (c: circuit) (w: int) : circuit = 
  (* FIXME: default behaviour when size of extenion < cur size or EC catches that case? *)
  (* assert(size_of_circ c.circ <= w); *)
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
    | [], _ 
    | _, [] -> assert false
    | r, BWInput (_, w)::cs -> let r1, r2 = List.takedrop w r in
      (BWCirc r1)::(doit r2 cs)
    | r, BWAInput (_, sz)::cs -> let r1, r2 = List.takedrop (size_of_asize sz) r in
      let r1 = List.chunkify sz.wordsize r1 |> Array.of_list in
      (BWArray r1)::(doit r2 cs)
    | r, BWTInput (_, sz)::cs ->
      let r, tp = List.fold_left_map (fun r sz -> 
        let comp, r = List.takedrop sz r in
        r, comp
      ) r sz.wordsizes
      in
      (BWTuple tp)::(doit r cs)
  in
  doit r inps, BWInput (idn, bsize)

(* Transforms the input for the circuit given into a big bitstring 
   (by concat + flatten of the previous inputs )*)
let circuit_aggregate_inps (c: circuit) : circuit = 
  match c.inps with
  | [] -> c
  | BWInput _ :: [] -> c
  | inps -> 
    let circs, inp = bus_of_cinputs inps in
    {circ=apply c circs; inps=[inp]}

(* 
  Array slices
  out_sz = size of out array (base size = input array base size)
  i = start_index
*)
let circuit_array_sliceget ~(wordsize : width) (arr_sz : width) (out_sz: width) (i: int) : circuit = 
  (* FIXME: Should be caught on EC side *)
  (* assert (arr_sz >= out_sz + i); *)
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
  (* FIXME: Should be caught on EC side *)
  (* assert (arr_sz >= out_sz + i); *)
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
  (* FIXME: Should be caught on EC side *)
  (* assert (arr_sz*el_sz >= i + acc_sz); *)
  let arr_inp = bwainput_of_size ~nelements:arr_sz ~wordsize:el_sz in
  let arr_id = (ident_of_cinput arr_inp).id_tag in
  let out = List.init acc_sz (fun j -> C.input (arr_id, i+j)) in
  {circ=BWCirc out; inps=[arr_inp]}

(* To be removed when we have external op bindings *)
let circuit_bwarray_slice_set (arr_sz: width) (el_sz: width) (acc_sz: int) (i: int) : circuit =
  (* FIXME: Should be caught on EC side *)
  (* assert (arr_sz*el_sz >= i + acc_sz); *)
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

let circuit_tuple_proj (c: circuit) (i: int) : circuit = 
  match c.circ with
  | BWTuple tp -> begin try
    {c with circ=BWCirc (List.at tp i)}
    with Invalid_argument e -> 
      let err = Format.sprintf "Projection at component %d outside tuple size (%d)@." i (List.length tp) in
      raise (CircError err)
    end
  | _ -> raise (CircError "Projection on non-tuple type")

let circuit_ueq (c: circuit) (d: circuit) : circuit =
  match c.circ, d.circ with
  | BWCirc r1, BWCirc r2 -> {circ= BWCirc[C.bvueq r1 r2]; inps=c.inps @ d.inps}
  | BWArray a1, BWArray a2 -> let elems = Array.map2 C.bvueq a1 a2 in
    {circ= BWCirc[C.ands (Array.to_list elems)]; inps=c.inps @ d.inps}
  | BWTuple t1, BWTuple t2 -> let elems = List.map2 C.bvueq t1 t2 in
    {circ= BWCirc[C.ands elems]; inps=c.inps @ d.inps}
  | _ -> raise (CircError "Mismatched types for ueq")

(* 
  f : BV1 -> BV2 
  a : BV1 Arr
  returns: BV2 Array = mapping f over a
*)
let circuit_map (f: circuit) (a: circuit) : circuit =
  let a, inps = try 
    destr_bwarray a.circ, a.inps 
  with CircError _ ->
    raise (CircError "Argument to circuit map is not bwarray")
  in
  let r = Array.map (fun r -> apply f [BWCirc r]) a in
  let r = Array.map (destr_bwcirc) r in
  {circ = BWArray r; inps}

let circuit_split ?(perm: (int -> int) option) (f: circuit) (lane_in_w: int) (lane_out_w: int) : circuit list =
  (* FIXME: Allow bdep for multiple inputs? *)
  if (List.length f.inps <> 1) 
  then raise (CircError "Multi input circuit split not supported")
  else

  try
    let r = destr_bwcirc f.circ in
    let inp_t, inp_w = List.hd f.inps |> destr_bwinput in 
    (*assert ((inp_w mod lane_in_w = 0) && (List.length r mod lane_out_w = 0));*)
    let rs = List.chunkify (lane_out_w) r in
    let rs = match perm with
      | Some perm -> List.filteri_map (fun i _ -> let idx = (perm i) in
        if idx < 0 || idx > (List.length rs) then None else
        Some (List.nth rs (idx))) rs
      | None -> rs
    in
    let rs = List.mapi (fun lane_idx lane_circ -> 
      let id = create ("split_" ^ (string_of_int lane_idx)) in
      let map_ = (function 
        | (v, j) when v = inp_t.id_tag 
            && (0 <= (j - (lane_idx*lane_in_w)) && (j-(lane_in_w*lane_idx)) < lane_in_w) 
            -> Some (C.input (id.id_tag, j - (lane_idx*lane_in_w))) 
        | _ -> None
        ) in
      let circ = BWCirc(C.maps map_ lane_circ) in
      {circ; inps=[BWInput(id, lane_in_w)]}
    ) rs in
    rs
  with 
  | CircError "destr_bwcirc" ->
    raise (CircError "Cannot split array or tuple")
  | CircError "destr_bwinput" ->
    raise (CircError "Cannot split non bitstring input")
    

(* Partitions into blocks of type n -> m *)
let circuit_mapreduce ?(perm: (int -> int) option) (c: circuit) (n:int) (m:int) : circuit list =
  let tm = Unix.gettimeofday () in
  Format.eprintf "[W] Beginning dependency analysis@.";
  let const_inp = BWInput (create "const", n) in
  let c = circuit_flatten c in
  let c = circuit_aggregate_inps c in
  let r = try destr_bwcirc c.circ 
    with CircError _ -> raise (CircError "Cannot mapreduce on non-bitstring return type") 
  in
  let deps = HL.deps r in
  let deps = HL.split_deps m deps in

  if not ((HL.block_list_indep deps) && (List.for_all (HL.check_dep_width n) (List.snd deps)))
  then
    raise (CircError "Failed mapreduce split (dependency split condition not true)")
  else

  Format.eprintf "[W] Dependency analysis complete after %f seconds@."
  (Unix.gettimeofday () -. tm);
  
  let cs = circuit_split ?perm c n m in
  List.map (function
    | {circ=BWCirc r; inps=[BWInput (idn, w)]}
      -> {circ=BWCirc (C.uextend ~size:m r); inps=[BWInput (idn, n)]}
    | {circ=BWCirc r; inps=[]}
      -> {circ=BWCirc (C.uextend ~size:m r); inps=[const_inp]}
    | c -> let err = Format.sprintf "Failed for %s@." (circuit_to_string c) in 
      raise (CircError err))
  cs

(* Build a circuit function that takes an input n bits wide and permutes 
  it in blocks of w bits by the permutation given by f 
  Expects that w | n and that f|[n/w] is a bijection *)
let circuit_permutation (n: int) (w: int) (f: int -> int) : circuit = 
  if (n mod w <> 0) then
    let err = Format.sprintf "In circuit permutation, block size (%d) does not divide circuit size (%d)@." w n in
    raise (CircError err)
  else
  (* FIXME: Permutation check should come from EC *)
  (* assert ( List.init (n/w) f |> Set.of_list |> Set.map f |> Set.cardinal = (n/w)); *)
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
      {circ = BWCirc(C.umod c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

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

    | Some { kind = `Rol  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.rol c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

    | Some { kind = `Ror  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.ror c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

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

    | Some { kind = `Xor  size } -> 
      let id1 = EcIdent.create (temp_symbol) in
      let id2 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      let c2 = C.reg ~size ~name:id2.id_tag in
      {circ = BWCirc(C.lxor_ c1 c2); inps = [BWInput(id1, size); BWInput(id2, size)]}

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
      (* assert (size <= out_size); *)
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.uextend ~size:out_size c1); inps = [BWInput (id1, size)]}

    | Some { kind = `Extend (size, out_size, true) } ->
      (* assert (size <= out_size); *)  
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size ~name:id1.id_tag in
      {circ = BWCirc(C.sextend ~size:out_size c1); inps = [BWInput (id1, size)]}

    | Some { kind = `Truncate (size, out_sz) } ->
      (* assert (size >= out_sz); *)
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size:out_sz ~name:id1.id_tag in
      { circ = BWCirc(c1); inps=[BWInput (id1, size)]}

    | Some { kind = `Concat (sz1, sz2, szo) } ->
      (* assert (sz1 + sz2 = szo); *)
      let id1 = EcIdent.create (temp_symbol) in
      let c1 = C.reg ~size:sz1 ~name:id1.id_tag in
      let id2 = EcIdent.create (temp_symbol) in
      let c2 = C.reg ~size:sz2 ~name:id2.id_tag in
      { circ = BWCirc(c1 @ c2); inps=[BWInput (id1, sz1); BWInput (id2, sz2)]}

    | Some { kind = `A2B ((w, n), m)} ->
      (* assert (n * w = m); *)
      let id1 = EcIdent.create temp_symbol in
      let c1 = C.reg ~size:m ~name:id1.id_tag in
      { circ = BWCirc(c1); inps = [BWAInput (id1, { nelements = n; wordsize = w })]}

    | Some { kind = `B2A (m, (w, n))} ->
      (* assert (n * w = m); *)
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
  let fg = 
    if strict then begin
      if circ_shape_equal f.circ g.circ then Some (f, g)
      else None
    end
    else if size_of_circ f.circ < size_of_circ g.circ then
      Some (circuit_bw_zeroextend f (size_of_circ g.circ), g) else
      Some (f, circuit_bw_zeroextend g (size_of_circ f.circ))
  in
  if Option.is_none fg then false
  else
  let f, g = Option.get fg in
  (* FIXME: more general input unification procedure ? *)  
  let pcond = match pcond with
  | Some pcond -> pcond
  | None -> {circ = BWCirc [C.true_]; inps = f.inps}
  in
  match unify_inputs [f;g;pcond] with
  | None -> Format.eprintf "Failed to merge inputs %s %s %s@." (circuit_to_string f) (circuit_to_string g) (circuit_to_string pcond); false
  | Some [{circ=BWCirc fcirc; _} as f;
    {circ=BWCirc gcirc; _};
    {circ=BWCirc pccirc; _}] ->
    begin
      (List.for_all2 (==) fcirc gcirc) ||
      let module B = (val HL.makeBWZinterface ()) in
      begin
      try 
        B.circ_equiv fcirc gcirc (List.hd pccirc) 
        (List.map (fun inp -> let a, b = destr_bwinput inp in
        (a.id_tag, b)) f.inps)
      with CircError "destr_bwinput" ->
        raise (CircError "Non-bitstring input in equiv call")  
      end
      (* Assuming no array inputs for now *)
    end
  | _ -> assert false

(* FIXME: TODO: Transfer this to EcEnv/wherever else appropriate *)
let op_cache = ref Mp.empty

type pstate = (symbol, circuit) Map.t
type cache  = (ident, (cinput * circuit)) Map.t

let circuit_of_form 
  ?(pstate  : pstate = Map.empty) (* Program variable values *)
   (hyps    : hyps) 
   (f_      : EcAst.form) 
  : circuit =
  let cache = Map.empty in

  let rec doit (cache: (ident, (cinput * circuit)) Map.t) (hyps: hyps) (f_: form) : hyps * circuit = 
    let env = toenv hyps in
    let redmode = circ_red hyps in
    (* let redmode = {redmode with delta_p = fun _ -> `No} in *)
    let fapply_safe f fs = 
      let res = EcTypesafeFol.fapply_safe ~redmode hyps f fs in
      res
    in

    let int_of_form (f: form) : zint = 
      match f.f_node with 
      | Fint i -> i
      | _ -> begin 
        try destr_int @@ EcCallbyValue.norm_cbv EcReduction.full_red hyps f
        with DestrError "int" ->
          let err = Format.asprintf "Failed to reduce form | %a | to integer"
            (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f in
          raise (CircError err)
        end
    in

    match f_.f_node with
    | Fint z -> raise (CircError "Translation encountered unexpected integer value")

    (* Assumes no quantifier bindings/new inputs within if *)
    | Fif (c_f, t_f, f_f) -> 
        let hyps, c_c = doit cache hyps c_f in
        let hyps, t_c = doit cache hyps t_f in
        let hyps, f_c = doit cache hyps f_f in

        if (try (List.length (destr_bwcirc c_c.circ) <> 1) 
          with CircError "destr_bwcirc" ->
            raise (CircError "Condition circuit should output a bitstring of size 1")
        ) then raise (CircError "Condition circuit output size too big")

        else
        let c_c = List.hd (destr_bwcirc c_c.circ) in
        (* inps = [] since we disallow definitions/quantifiers inside conditionals *)
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
            inps = []; 
          }
        | BWTuple t_tp, BWTuple f_tp when (List.compare_lengths t_tp f_tp = 0) ->
            hyps, {
            circ = BWTuple (List.map2 (C.ite c_c) t_tp f_tp);
            inps = [];
          }
        | _ -> raise (CircError "Type mismatch between conditional arms")
        (* EC should prevent this as equal EC types ==> equal circuit types *)
        end
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
            let err = Format.sprintf "Unsupported op kind%s@." (EcPath.tostring pth) in
            raise (CircError err)
        end
        in 
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ
    end
    | Fapp _ -> 
    (* TODO: find a way to properly propagate int arguments *)

    (* let f_ = apply_int_args f_ in *)
    let (f, fs) = EcCoreFol.destr_app f_ in
    let hyps, res = 
      (* Assuming correct types coming from EC *)
      (* FIXME: Add some extra info about errors when something here throws *)
      match EcEnv.Circuit.reverse_operator env @@ (EcCoreFol.destr_op f |> fst) with
      | `Array ({ size }, `Get) :: _ -> let hyps, res = 
        match fs with
        | [arr; i] ->
          let i = int_of_form i in
          let (_, t) = Option.get_exn (destr_array_type env arr.f_ty) (CircError "Array get type error") in
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
        let n, w = 
          match EcEnv.Circuit.lookup_array_and_bitstring env f_.f_ty with
          | Some ({size=asize}, {size=bwsize}) -> asize, bwsize
          | None -> raise (CircError "Array of_list type error (wrong binding?)")
        in
        let dfl, vs = match fs with
          | [dfl; vs] -> dfl, vs 
          | _ -> assert false 
          (* This should be caught by the EC typecheck/bindings so never actually happens *)
        in
        let vs = try EcCoreFol.destr_list vs 
          with DestrError _ -> raise (CircError "Failed to destructure list argument to array of_list")
        in
        let hyps, vs = List.fold_left_map (doit cache) hyps vs in
        begin match EcCoreFol.is_witness dfl with
        | false -> 
          let hyps, dfl = doit cache hyps dfl in
          if not (List.is_empty dfl.inps && List.for_all (fun c -> List.is_empty c.inps) vs) then
            raise (CircError "Definitions inside of_list call not supported")
          else
          begin try 
            let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
            let dfl = destr_bwcirc dfl.circ in
            let r = Array.init n (fun i -> List.nth_opt vs i |> Option.default dfl) in
            hyps, {circ = BWArray r; inps = []}
          with CircError "destr_bwcirc" ->
            raise (CircError "BWCirc destruct error in array of_list ")
          end
        | true -> 
          if not (List.compare_length_with vs n = 0) then
            raise (CircError "Insufficient list length for of_list with default = witness")
          else
          if not (List.for_all (fun c -> List.is_empty c.inps) vs) then
            raise (CircError "Definitions inside of_list not supported")
          else
          begin try
            let vs = List.map (fun c -> destr_bwcirc c.circ) vs in
            let r = Array.of_list vs in
            hyps, {circ=BWArray r; inps=[]}
          with CircError _ ->
            raise (CircError "BWCirc destruct error in array of_list ")
          end
        end
      | `Bitstring ({ size }, `OfInt) :: _ ->
        let i = match fs with
        | f :: _ -> int_of_form f
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in 
        hyps, { circ = BWCirc (C.of_bigint_all ~size (to_zt i)); inps = [] }
      | `BvOperator ({ kind = `Extract (size, out_sz) }) :: _ ->
        (* assert (size >= out_sz); *)
        (* Should never happen, caught in EC typecheck/bindings *)        
        let c1, b = match fs with
        | [c; f] -> c, int_of_form f
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in
        let hyps, c1 = doit cache hyps c1 in
        let c = try destr_bwcirc c1.circ 
          with CircError _ -> raise (CircError "destr error at bvextract")
        in
        let c = List.take out_sz (List.drop (to_int b) c) in
        hyps, { circ = BWCirc(c); inps=c1.inps }
      | `BvOperator ({kind = `Init (size)}) :: _ ->
        let f = match fs with
        | [f] -> f
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in
        let fs = List.init size (fun i -> fapply_safe f [f_int (of_int i)]) in
        (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)
        let hyps, fs = List.fold_left_map (doit cache) hyps fs in
        hyps, circuit_aggregate fs
      | `BvOperator ({kind = `Get (size)}) :: _ ->
        let bv, i = match fs with
        | [bv; i] -> bv, int_of_form i |> to_int
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in
        (* assert (i < size); *)
        (* Should never happen, caught in EC typecheck/bindings *)
        let hyps, bv = doit cache hyps bv in
        let bv_base = try destr_bwcirc bv.circ 
          with CircError _ -> raise (CircError "BWCirc destr error at bvget") 
        in
        hyps, {bv with circ = BWCirc([List.nth bv_base i])}
        
      | `BvOperator ({kind = `AInit (arr_sz, bw_sz)}) :: _ ->
        let f = match fs with
        | [f] -> f
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in
        let fs = List.init arr_sz (fun i -> fapply_safe f [f_int (of_int i)]) in
        (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)
        let hyps, fs = List.fold_left_map (doit cache) hyps fs in
        if not (List.for_all (fun c -> List.is_empty c.inps) fs) then
          raise (CircError "Quantifiers/Definitions inside init lambda not supported")
        else
        begin try 
        hyps, {circ = BWArray(Array.of_list (List.map (fun c -> destr_bwcirc c.circ) fs)); inps=[]}
          with CircError _ -> raise (CircError "Array elements in init should be bitstrings")
        end

      | `BvOperator ({kind = `Map (sz1, sz2, asz)}) :: _ -> 
        let f, a = match fs with
        | [f; a] -> f, a
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in 
        let hyps, f = doit cache hyps f in
        let hyps, a = doit cache hyps a in
        hyps, circuit_map f a

      | `BvOperator ({kind = `ASliceGet ((arr_sz, sz1), sz2)}) :: _ ->
        let arr, i = match fs with
        | [arr; i] -> arr, int_of_form i
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
        in
        let op = circuit_bwarray_slice_get arr_sz sz1 sz2 (to_int i) in
        let hyps, arr = doit cache hyps arr in
        hyps, compose op [arr]
        
      | `BvOperator ({kind = `ASliceSet ((arr_sz, sz1), sz2)}) :: _ ->
        let arr, i, bv = match fs with
        | [arr; i; bv] -> arr, int_of_form i, bv
        | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)
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
            (* assert (List.compare_lengths r1 r2 = 0); *)
            (* Should never happen, caught in EC typecheck/bindings *)
            hyps, {circ = BWCirc([C.bvueq r1 r2]); inps=merge_inputs c1.inps c2.inps} 
            (* FIXME: Do we allow quantifiers/definitions inside equality sides? *)
          | BWArray a1, BWArray a2 -> 
            (* assert (Array.for_all2 (fun a b -> (List.compare_lengths a b) = 0) a1 a2); *)
            (* Should never happen, caught in EC typecheck/bindings *)
            if not (Array.length a1 = Array.length a2) then
              raise (CircError "Comparison between arrays of different size")
            else
            let rs = Array.map2 C.bvueq a1 a2 in
            hyps, {circ = BWCirc([C.ands (Array.to_list rs)]); inps = merge_inputs c1.inps c2.inps}
          | _ -> assert false
          end
        | Some `True, [] ->
          hyps, {circ = BWCirc([C.true_]); inps=[]}
        | Some `False, [] ->
          hyps, {circ = BWCirc([C.false_]); inps=[]}
        (* recurse down into definition *)
        | _ -> 
          (* let f, fs = destr_app (apply_int_args f_) in *)
          let hyps, f_c = doit cache hyps f in
          let hyps, fcs = List.fold_left_map
            (doit cache)
            hyps fs 
          in
          hyps, compose f_c fcs
        (* | _ -> Format.eprintf "Problem at %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f_; *)
          (* assert false *)
        end
      in hyps, res
      
    | Fquant (qnt, binds, f) -> 
      let binds = List.map (fun (idn, t) -> cinput_of_type ~idn env (gty_as_ty t)) binds in
      let cache = List.fold_left 
        (fun cache inp -> 
          let circ = {(circ_ident inp) with inps = []} in
          Map.add (ident_of_cinput inp) (inp, circ) cache) cache binds in
      let hyps, circ = doit cache hyps f in
      begin match qnt with
      | Llambda -> hyps, {circ with inps=binds @ circ.inps} 
      | Lforall 
      | Lexists -> raise (CircError "Universal/Existential quantification not supported ")
      (* TODO: figure out how to handle quantifiers *)
      end
    | Fproj (f, i) ->
        let hyps, ftp = doit cache hyps f in
        hyps, circuit_tuple_proj ftp i
    | Fmatch  (f, fs, ty) -> raise (CircError "Match not supported")
    | Flet    (lpat, v, f) -> 
      begin match lpat with
      | LSymbol (idn, ty) -> 
        let hyps, vc = doit cache hyps v in
        let inp = cinput_of_type ~idn env ty in
        let () = assert (match_arg inp vc.circ) in
        let cache = Map.add idn (inp, vc) cache in
        doit cache hyps f
      | LTuple  symbs -> 
        let hyps, tp = doit cache hyps v in
        let comps = if is_bwtuple tp.circ 
          then circuits_of_circuit tp
          else raise (CircError "tuple let type error")
        in
        
        (* Assuming types match coming from EC *)
        let cache = List.fold_left2 (fun cache (idn, ty) c -> 
          let inp = cinput_of_type ~idn env ty in
          Map.add idn (inp, c) cache) cache symbs comps 
        in
        doit cache hyps f
        
      | LRecord (pth, osymbs) -> raise (CircError "record types not supported")
      end
    | Fpvar   (pv, mem) -> 
      let v = match pv with
      | PVloc v -> v
      | _ -> raise (CircError "Global vars not supported")
      (* FIXME: Should globals be supported? *)
      in
      let res = match Map.find_opt v pstate with
        | Some circ -> circ
        | None -> raise (CircError (Format.sprintf "Uninitialized program variable %s" v))
        (* FIXME: Do we add support for initialized PVs? With a check at the end that 
                  the result does not depend on their value *)
      in hyps, res
    | Fglob   (id, mem) -> raise (CircError "glob not supported")
    | Ftuple  comps -> 
      let hyps, comps = 
        List.fold_left_map (fun hyps comp -> doit cache hyps comp) hyps comps 
      in
      (* FIXME: Change to inps = [] if we disallow definitions/quantifiers inside tuples *)
      let inps = List.fold_right merge_inputs (List.map (fun c -> c.inps) comps) [] in
      let comps = List.map (fun c -> destr_bwcirc c.circ) comps in
      hyps, {circ= BWTuple comps; inps}
    | _ -> raise (CircError "Unsupported form kind in translation")


  in 
  let hyps, f_c = doit cache hyps f_ in
  f_c


let circuit_of_path (hyps: hyps) (p: path) : circuit =
  let f = EcEnv.Op.by_path p (toenv hyps) in
  let f = match f.op_kind with
  | OB_oper (Some (OP_Plain f)) -> f
  | _ -> raise (CircError "Invalid operator type")
  in
  circuit_of_form hyps f

(* For program generation, input is passed outside of circuit since it is only set at end of generation *)
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

let process_instr (hyps: hyps) (mem: memory) (pstate: _) (inst: instr) =
  let env = toenv hyps in
  (* Format.eprintf "[W]Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst; *)
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) -> 
      let pstate = Map.add v (form_of_expr mem e |> circuit_of_form ~pstate hyps) pstate in
      (* Format.eprintf "[W] Took %f seconds@." (Unix.gettimeofday() -. start); *)
      pstate
    | Sasgn (LvTuple (vs), e) ->
      let tp = (form_of_expr mem e |> circuit_of_form ~pstate hyps) in
      assert (is_bwtuple tp.circ);
      let comps = circuits_of_circuit tp in
      let pstate = List.fold_left2 (fun pstate (pv, _ty) c -> 
        let v = match pv with
        | PVloc v -> v
        | _ -> raise (CircError "Global variables not supported")
        in
        Map.add v c pstate
        ) pstate vs comps
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
  ?(pstate     : _ = Map.empty    )
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

  let pstate = List.map (fun (pv, ty) -> { v_name = EcTypes.get_loc pv; v_type = ty; }) (rd @ wr) in
  let pstate, inputs = pstate_of_variables env pstate in

  let pstate1 = List.fold_left (process_instr hyps mem) pstate s1 in
  let pstate2 = List.fold_left (process_instr hyps mem) pstate s2 in
  match keep with
  | Some pv -> 
    let vs = EcPV.PV.elements pv |> fst in
    let vs = List.map (function 
      | (PVloc v, ty) -> (v, ty)
      | _ -> raise (CircError "global variables not supported")
      ) vs 
    in List.for_all (fun (var, ty) -> 
      let circ1 = Map.find_opt var pstate1 in
      let circ2 = Map.find_opt var pstate2 in
      match circ1, circ2 with
      | None, None -> true
      | None, Some circ1
      | Some circ1, None -> 
        let circ2 = Map.find_opt var pstate in
        if Option.is_none circ2 then assert false (* Should never happen (do we return false if it does?) FIXME *)
        else
          let circ1 = {circ1 with inps = inputs @ circ1.inps} in
          let circ2 = Option.get circ2 in
          let circ2 = {circ2 with inps = circ1.inps } in
          circ_equiv circ1 circ2 None
      | Some circ1, Some circ2 ->
      let circ1 = { circ1 with inps = inputs @ circ1.inps } in
      let circ2 = { circ2 with inps = inputs @ circ2.inps } in
      circ_equiv circ1 circ2 None
    ) vs
  | None -> Map.keys pstate |> Enum.for_all (fun var -> 
    let circ1 = Map.find var pstate1 in
    let circ1 = { circ1 with inps = inputs @ circ1.inps } in
    let circ2 = Map.find var pstate2 in
    let circ2 = { circ2 with inps = inputs @ circ2.inps } in
    circ_equiv circ1 circ2 None
  )

let initial_pstate_of_vars (env: env) (invs: variable list) : cinput list * (symbol, circuit) Map.t =
  let pstate : (symbol, circuit) Map.t = Map.empty in

  let inps = List.map (input_of_variable env) invs in
  let inpcs, inps = List.split inps in
  (* List.iter (fun c -> Format.eprintf "Inp: %s @." (cinput_to_string c)) inps; *)
  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) invs in

  inps, List.fold_left 
    (fun pstate (inp, v) -> Map.add v inp pstate)
    pstate inpcs 

    (* Generates pstate : (symbol, circuit) Map from program 
  and inputs associated to the program
        Throws: CircError on failure 
       *)
let pstate_of_prog (hyps: hyps) (mem: memory) (proc: instr list) (invs: variable list) : (symbol, circuit) Map.t =
  let inps, pstate = initial_pstate_of_vars (toenv hyps) (invs) in

  let pstate = 
    List.fold_left (process_instr hyps mem) pstate proc
  in
  Map.map (fun c -> assert (c.inps = []); {c with inps=inps}) pstate 

let pstate_get (pstate: pstate) (v: symbol) : circuit = 
  try
    Map.find v pstate  
  with Not_found ->
    raise (CircError (Format.sprintf "No circuit in state for name %s@." v))

let pstate_get_all (pstate: pstate) : circuit list = 
  Map.values pstate |> List.of_enum

(* FIXME: refactor this function *)
let rec circ_simplify_form_bitstring_equality
  ?(mem = mhr) 
  ?(pstate: (symbol, circuit) Map.t = Map.empty) 
  ?(pcond: circuit option)
  (hyps: hyps) 
  (f: form)
  : form =
  let env = toenv hyps in

  let rec check (f : form) =
    match EcFol.sform_of_form f with
    | SFeq (f1, f2)
         when (Option.is_some @@ EcEnv.Circuit.lookup_bitstring env f1.f_ty)
           || (Option.is_some @@ EcEnv.Circuit.lookup_array env f1.f_ty)
      ->
      let c1 = circuit_of_form ~pstate hyps f1 in
      let c2 = circuit_of_form ~pstate hyps f2 in
      Format.eprintf "[W]Testing circuit equivalence for forms:
      %a@.%a@.With circuits: %s | %s@."
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f1
      (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f2
      (circuit_to_string c1)
      (circuit_to_string c2);
      f_bool (circ_equiv c1 c2 pcond)
    | _ -> f_map (fun ty -> ty) check f 
  in check f
