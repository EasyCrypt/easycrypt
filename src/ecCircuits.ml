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
exception CircError of string

let width_of_type (env: env) (t: ty) : int =
  match EcEnv.Circuit.lookup_array_and_bitstring env t with
  | Some ({size=size_arr}, {size=size_bs}) -> size_arr * size_bs
  | _ -> match EcEnv.Circuit.lookup_bitstring_size env t with
    | Some w -> w
    | None -> let err = Format.asprintf "No bitvector binding for type %a@."
    (EcPrinting.pp_type (EcPrinting.PPEnv.ofenv env)) t in 
    raise (CircError err)

module AIG_Backend = struct
  type asize = { wordsize: int; nelements: width; }

  type tpsize = { wordsizes : int list; npos : width; }

  let size_of_asize (sz : asize) : int =
    sz.wordsize * sz.nelements

  let size_of_tpsize (sz : tpsize) : int =
    List.sum sz.wordsizes


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

end

(* FIXME: TODO: Transfer this to EcEnv/wherever else appropriate *)
exception CircError of string

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
  type circuit = circ * (cinp list)
  
  module CArgs : sig
    type arg 

    val arg_of_circuit : circuit -> arg
    val arg_of_zint : zint -> arg
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


  (* Circuits representing booleans *)
  val circuit_true : (cbool * (cinp list)) 
  val circuit_false : (cbool * (cinp list)) 

  (* <=> circuit has not inputs (every input is unbound) *)
  val circuit_is_free : circuit -> bool
  
  (* Direct circuuit constructions *)
  val circuit_ite : c:(cbool * (cinp list)) -> t:circuit -> f:circuit -> circuit
  val circuit_eq : circuit -> circuit -> circuit

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

  (* Circuit equivalence call, should do some processing and then call some backend *)
  val circ_equiv : ?pcond:(cbool * (cinp list)) -> circuit -> circuit -> bool

  (* Composition of circuit functions, should deal with inputs and call some backend *)
  val circuit_compose : circuit -> circuit list -> circuit

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

  val node_array_of_reg : reg -> node array
  val node_list_of_reg : reg -> node list
  val reg_of_node_list : node list -> reg
  val reg_of_node_array : node array -> reg

  val apply : (inp -> node option) -> node -> node
  val circuit_from_spec : Lospecs.Ast.adef -> reg list -> reg 

  val input_node : id:int -> int -> node
  val input_of_size : ?offset:int -> id:int -> int -> reg

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
end

module TestBack : CBackend = struct
  type node = C.node
  type reg = C.node array
  type inp = int * int

  let true_ = C.true_
  let false_ = C.false_

  let node_array_of_reg : reg -> node array = fun x -> x
  let node_list_of_reg : reg -> node list = fun x -> Array.to_list x  
  let reg_of_node_list : node list -> reg = fun x -> Array.of_list x
  let reg_of_node_array : node array -> reg = fun x -> x

  let node_eq (n1: node) (n2: node) = C.xnor n1 n2
  let ite (c: node) (t: node) (f: node) = C.mux2 f t c 

  let band : node -> node -> node = 
    C.and_

  let bor : node -> node -> node = 
    C.or_

  let bxor : node -> node -> node = 
    C.xor

  let bnot : node -> node = 
    C.neg

  let bxnor : node -> node -> node = 
    C.xnor

  let bnand : node -> node -> node = 
    C.nand

  let bnor : node -> node -> node = 
    fun n1 n2 -> C.neg @@ C.or_ n1 n2 

  (* FIXME: maybe convert to BigInt? *)
  let input_node ~id i = C.input (id, i)
  let input_of_size ?(offset = 0) ~id (i: int) = Array.init i (fun i -> C.input (id, offset + i))

  let apply = assert false
  let circuit_from_spec = assert false

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

  (* arg for circuit construction *)
  module CArgs = struct
    type arg = 
    [ `Circuit of circuit
    | `Constant of zint   
    | `Init of int -> circuit]
    let arg_of_circuit c = 
      `Circuit c
    let arg_of_zint z =
      `Constant z
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

    let empty_pstate : pstate = assert false

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

  let circuit_input_compatible ((c, _): circuit) (cinp: cinp) : bool =
    match c, cinp with
    | `CBitstring r, { type_ = `CIBitstring w } when Array.length r = w -> true
    | `CArray (r, w), { type_ = `CIArray (w', n)} when Array.length r = w'*n && w = w' -> true
    | `CTuple (r, szs), { type_ = `CITuple szs' } when szs = szs' -> true
    | `CBool _, { type_ = `CIBool } -> true
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
    let id = match name with 
    | `Str name -> EcIdent.create name |> tag 
    | `Idn idn -> tag idn 
    in
    let inp = Backend.input_node ~id 0 in
    `CBool inp, { type_ = `CIBool; id; }

  let new_cbitstring_inp ?(name = `Str "input") (sz: int) : cbitstring * cinp =
    let id = match name with 
    | `Str name -> EcIdent.create name |> tag 
    | `Idn idn -> tag idn 
    in
    let inp = Backend.input_of_size ~id sz in
    `CBitstring (Backend.node_array_of_reg inp), 
    { type_ = `CIBitstring sz; id; }

  let new_carray_inp ?(name = `Str "input") (el_sz: int) (arr_sz: int) : carray * cinp = 
    let id = match name with 
    | `Str name -> EcIdent.create name |> tag 
    | `Idn idn -> tag idn 
    in
    let inp = Backend.input_of_size ~id (el_sz * arr_sz) in
    `CArray (Backend.node_array_of_reg inp, el_sz), 
    { type_ = `CIArray (el_sz, arr_sz); id; } 

  let new_ctuple_inp ?(name = `Str "input") (szs: int list) : ctuple * cinp =
    let id = match name with 
    | `Str name -> EcIdent.create name |> tag 
    | `Idn idn -> tag idn 
    in
    let inp = Backend.input_of_size ~id (List.sum szs) in
    `CTuple (Backend.node_array_of_reg inp, szs),
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

  let circuit_eq (c: circuit) (d: circuit) : circuit =  
    match c, d with
    | (`CArray (r1, _), inps1), (`CArray (r2, _), inps2) 
    | (`CTuple (r1, _), inps1), (`CTuple (r2, _), inps2) 
    | (`CBitstring r1, inps1), (`CBitstring r2, inps2) ->
        `CBitstring [|(Array.fold (Backend.band) Backend.true_ (Array.map2 (fun c d -> Backend.node_eq c d) r1 r2))|], merge_inputs inps1 inps2 
    | _ -> assert false
    
  (* 
  module Backend = struct
    type circ_ = C.reg
    type circ = { backing: circ_; 
                  ty: [ `CBitstring of int 
                      | `CArray of int * int 
                      | `CTuple of int * int list]
      } 
    type node = C.node

    let circ_of_node : node -> circ = assert false
    let circ_of_node : node -> circ = assert false
    module CBitstring = struct
      type cbitstring = [`CBitstring of int * circ_]
      let get (c: cbitstring) (i: int) : node = match c, i with 
        | `CBitstring (w, c), i when 0 <= i && i < w -> List.nth c i
        | _ -> raise (CircError "Bad BW get")
      let set (c: cbitstring) (i: int) (n: node) : cbitstring =
        match c with
        | `CBitstring (w, c) ->
          `CBitstring (w, List.mapi (fun j v -> if i == j then n else v) c)
    end
    module CArray = struct
      type carray = [`CArray of int * circ]
      let get : wordsize:int -> carray -> int -> circ = assert false
      let set : wordsize:int -> carray -> int -> circ -> carray = assert false 
    end
    module CTuple = struct
      type ctuple = [`CTuple of int * circ]
      let get : wordsize:int -> ctuple -> int -> circ = assert false
      let set : wordsize:int -> ctuple -> int -> circ -> ctuple = assert false 
    end
  end
 *)

  let circuit_compose (c: circuit) (args: circuit list) : circuit = 
    (try
      assert (List.for_all2 (fun c cinp -> circuit_input_compatible c cinp) args (snd c))
    with 
      Assert_failure _ -> assert false
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
  let op_is_base (env: env) (p: path) : bool = 
    not @@ List.is_empty @@ EcEnv.Circuit.reverse_operator env p 

  let op_is_parametric_base (env: env) (p: path) : bool =
    assert false
 
  module BaseOps = struct
    let temp_symbol = "temp_circ_input"
    
    let is_of_int (env: env) (p: path) : bool = 
      match EcEnv.Circuit.reverse_bitstring_operator env p with
      | Some (_, `OfInt) -> true
      | _ -> false

    let circuit_of_parametric_base (env : env) (op: [`Path of path | `BvBind of EcDecl.crb_bvoperator]) (args: arg list) : circuit =
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
      (* FIXME: what do we want for out of bounds extract? *)
      | { kind = `Extract (w_in, w_out) } -> 
        begin match args with
        | [ `Circuit (`CBitstring r, cinps) ; `Constant i ] ->
            (`CBitstring (Array.sub r (BI.to_int i) w_out), cinps) 
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
          let circs = List.map (function | `CBitstring r -> r | _ -> assert false) circs in
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


    let circuit_of_baseo (env: env) (op: [`Path of path | `BvBind of EcDecl.crb_bvoperator]) : circuit =
      assert false

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

      (* FIXME: should this be fully backend responsability or not?  *)
      | { kind = `Extend (size, out_size, false) } ->
        (* assert (size <= out_size); *)
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.uext c1 out_size |> Backend.node_array_of_reg), [inp1] 

      (* FIXME: should this be fully backend responsability or not?  *)
      | { kind = `Extend (size, out_size, true) } ->
        (* assert (size <= out_size); *)  
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.sext c1 out_size |> Backend.node_array_of_reg), [inp1] 

      (* FIXME: should this be fully backend responsability or not?  *)
      | { kind = `Truncate (size, out_sz) } ->
        (* assert (size >= out_sz); *)
        let c1, inp1 = new_cbitstring_inp size |-> ((fun c -> reg_of_circ (c:>circ)), idnt) in  
        `CBitstring (Backend.trunc c1 out_sz |> Backend.node_array_of_reg), [inp1] 

      (* FIXME: should this be fully backend responsability or not?  *)
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

      | { kind = `ASliceGet _ | `ASliceSet _ | `Extract _ | `Map _ | `AInit _ | `Get _ | `Init _  } -> assert false

      (* | _ -> raise @@ CircError "Failed to generate op"  *)


      
  end
  open BaseOps

  module BitstringOps = struct
    type binding = crb_bitstring_operator 

    let circuit_of_bsop (env: env) (op: [`Path of path | `BSBinding of binding]) : circuit =
      let op = match op with
      | `BSBinding bnd -> bnd
      | `Path p -> begin match EcEnv.Circuit.reverse_bitstring_operator env p with
        | Some bnd -> bnd
        | None -> assert false
        end
      in
      match op with
      | bs, `From -> assert false
      | bs, `OfInt -> assert false 
      | bs, `To -> assert false 
      | bs, `ToSInt -> assert false 
      | bs, `ToUInt -> assert false 
  end
  open BitstringOps

  module ArrayOps = struct
    type binding = crb_array_operator 

    let circuit_of_bsop (env: env) (op: [`Path of path | `BSBinding of binding]) : circuit =
      let op = match op with
      | `BSBinding bnd -> bnd
      | `Path p -> begin match EcEnv.Circuit.reverse_array_operator env p with
        | Some bnd -> bnd
        | None -> assert false
        end
      in
      match op with
      | (bs, `ToList) -> assert false
      | (bs, `Get) -> assert false
      | (bs, `OfList) -> assert false
      | (bs, `Set) -> assert false
  end
  open ArrayOps


  (*
    let open AIG_Backend in
    match EcEnv.Circuit.reverse_operator env p with
    | `Array ({ size }, `Get) :: _ -> 
      match args with
      | [`Circuit arr; `Constant i] ->
        
        compose (circuit_bwarray_get ~nelements:size ~wordsize:w (BI.to_int i)) [arr]
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

    assert false
  *)


  (* Circuit Lambda functions *)
  let rec circ_lambda_one (env:env) (idn: ident) (t: ty) : cinp * circuit = 
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

  let circ_equiv : ?pcond:(cbool * cinp list) -> circuit -> circuit -> bool = assert false

  module CircuitSpec = struct
    (* FIXME: do we ever have circuits coming from the spec that take or return arrays? *)
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


  let circuit_of_op (env: env) (p: path) : circuit = 
    let op = try
      EcEnv.Circuit.reverse_operator env p |> List.hd
    with Failure _ -> 
      assert false
    in
    match op with
    | `Bitstring (bs, op) -> assert false 
    | `Array _ -> assert false 
    | `BvOperator _ -> assert false 
    | `Circuit c -> circuit_from_spec env (`Bind c)
    
  let circuit_of_op_with_args (env: env) (p: path) (args: arg list) : circuit  = assert false

end

module ExampleInterface = MakeCircuitInterfaceFromCBackend(TestBack)
open ExampleInterface
open PState
open LocalCache
open CircuitSpec
open CArgs
(* FIXME: why are all these openings required? *)

let type_is_registered (env: env) (t: ty) : bool = 
  (Option.is_some (EcEnv.Circuit.lookup_array_and_bitstring env t)) ||
  (Option.is_some (EcEnv.Circuit.lookup_bitstring env t))

let op_cache = ref Mp.empty
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

    let process_arg (hyps: hyps) (f: form) : hyps * arg = 
      match f.f_ty with
      | t when t = EcTypes.tint -> hyps, arg_of_zint (int_of_form f)
      | t when type_is_registered (LDecl.toenv hyps) t -> 
          let hyps, f = doit cache hyps f in 
          hyps, arg_of_circuit f
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
        (* Format.eprintf "Using cached op: %s@." (EcPath.tostring pth); *)
        hyps, op
      | None -> 
        (* Format.eprintf "No cache for op: %s@." (EcPath.tostring pth); *)
      if op_is_base env pth then
        let circ = circuit_of_op env pth in
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ 
      (* else if op_has_spec env pth then
        let circ = circuit_from_spec env pth in
        op_cache := Mp.add pth circ !op_cache;
        hyps, circ *)
      else
        let hyps, circ = match (EcEnv.Op.by_path pth env).op_kind with
        | OB_oper (Some (OP_Plain f)) -> 
          doit cache hyps f
        | _ -> begin match EcFol.op_kind (destr_op f_ |> fst) with
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
    | Fapp _ -> 
    (* TODO: find a way to properly propagate int arguments *)
    (* FIXME: do this case *)
    (* let f_ = apply_int_args f_ in *)
    let (f, fs) = EcCoreFol.destr_app f_ in
    let hyps, args = List.fold_left_map (process_arg) hyps fs in 
    begin match f with
      | {f_node = Fop (pth, _)} when op_is_parametric_base env pth -> hyps, circuit_of_op_with_args env pth args
      | f ->
    let hyps, res = 
      (* Assuming correct types coming from EC *)
      (* FIXME: Add some extra info about errors when something here throws *)
      match EcEnv.Circuit.reverse_operator env @@ (EcCoreFol.destr_op f |> fst) with
      (*| `Array ({ size }, `Get) :: _ -> let hyps, res = *)
      (*  match fs with*)
      (*  | [arr; i] ->*)
      (*    let i = int_of_form i in*)
      (*    let (_, t) = Option.get_exn (destr_array_type env arr.f_ty) (CircError "Array get type error") in*)
      (*    let w = width_of_type env t in*)
      (*    let hyps, arr = doit cache hyps arr in*)
      (*    hyps, compose (circuit_bwarray_get ~nelements:size ~wordsize:w (BI.to_int i)) [arr]*)
      (*  | _ -> raise (CircError "set")*)
      (*  in hyps, res*)
      (*| `Array ({ size }, `Set) :: _ -> let hyps, res = *)
      (*  match fs with*)
      (*  | [arr; i; v] ->*)
      (*    let i = int_of_form i in*)
      (*    let w = width_of_type env v.f_ty  in*)
      (*    let hyps, arr = doit cache hyps arr in*)
      (*    let hyps, v = doit cache hyps v in*)
      (*    hyps, compose (circuit_bwarray_set ~nelements:size ~wordsize:w (BI.to_int i)) [arr; v]*)
      (*  | _ -> raise (CircError "set")*)
      (*  in hyps, res*)
      (*| `Array ({ size }, `OfList) :: _->*)
      (*  let n, w = *)
      (*    match EcEnv.Circuit.lookup_array_and_bitstring env f_.f_ty with*)
      (*    | Some ({size=asize}, {size=bwsize}) -> asize, bwsize*)
      (*    | None -> raise (CircError "Array of_list type error (wrong binding?)")*)
      (*  in*)
      (*  let dfl, vs = match fs with*)
      (*    | [dfl; vs] -> dfl, vs *)
      (*    | _ -> assert false *)
      (*    (* This should be caught by the EC typecheck/bindings so never actually happens *)*)
      (*  in*)
      (*  let vs = try EcCoreFol.destr_list vs *)
      (*    with DestrError _ -> raise (CircError "Failed to destructure list argument to array of_list")*)
      (*  in*)
      (*  let hyps, vs = List.fold_left_map (doit cache) hyps vs in*)
      (*  begin match EcCoreFol.is_witness dfl with*)
      (*  | false -> *)
      (*    let hyps, dfl = doit cache hyps dfl in*)
      (*    if not (List.is_empty dfl.inps && List.for_all (fun c -> List.is_empty c.inps) vs) then*)
      (*      raise (CircError "Definitions inside of_list call not supported")*)
      (*    else*)
      (*    begin try *)
      (*      let vs = List.map (fun c -> destr_bwcirc c.circ) vs in*)
      (*      let dfl = destr_bwcirc dfl.circ in*)
      (*      let r = Array.init n (fun i -> List.nth_opt vs i |> Option.default dfl) in*)
      (*      hyps, {circ = BWArray r; inps = []}*)
      (*    with CircError "destr_bwcirc" ->*)
      (*      raise (CircError "BWCirc destruct error in array of_list ")*)
      (*    end*)
      (*  | true -> *)
      (*    if not (List.compare_length_with vs n = 0) then*)
      (*      raise (CircError "Insufficient list length for of_list with default = witness")*)
      (*    else*)
      (*    if not (List.for_all (fun c -> List.is_empty c.inps) vs) then*)
      (*      raise (CircError "Definitions inside of_list not supported")*)
      (*    else*)
      (*    begin try*)
      (*      let vs = List.map (fun c -> destr_bwcirc c.circ) vs in*)
      (*      let r = Array.of_list vs in*)
      (*      hyps, {circ=BWArray r; inps=[]}*)
      (*    with CircError _ ->*)
      (*      raise (CircError "BWCirc destruct error in array of_list ")*)
      (*    end*)
      (*  end*)
      (*| `Bitstring ({ size }, `OfInt) :: _ ->*)
      (*  let i = match fs with*)
      (*  | f :: _ -> int_of_form f*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in *)
      (*  hyps, { circ = BWCirc (C.of_bigint_all ~size (to_zt i)); inps = [] }*)
      (*| `BvOperator ({ kind = `Extract (size, out_sz) }) :: _ ->*)
      (*  (* assert (size >= out_sz); *)*)
      (*  (* Should never happen, caught in EC typecheck/bindings *)        *)
      (*  let c1, b = match fs with*)
      (*  | [c; f] -> c, int_of_form f*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  let hyps, c1 = doit cache hyps c1 in*)
      (*  let c = try destr_bwcirc c1.circ *)
      (*    with CircError _ -> raise (CircError "destr error at bvextract")*)
      (*  in*)
      (*  let c = List.take out_sz (List.drop (to_int b) c) in*)
      (*  hyps, { circ = BWCirc(c); inps=c1.inps }*)
      (*| `BvOperator ({kind = `Init (size)}) :: _ ->*)
      (*  let f = match fs with*)
      (*  | [f] -> f*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  let fs = List.init size (fun i -> fapply_safe f [f_int (of_int i)]) in*)
      (*  (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)*)
      (*  let hyps, fs = List.fold_left_map (doit cache) hyps fs in*)
      (*  hyps, circuit_aggregate fs*)
      (*| `BvOperator ({kind = `Get (size)}) :: _ ->*)
      (*  let bv, i = match fs with*)
      (*  | [bv; i] -> bv, int_of_form i |> to_int*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  (* assert (i < size); *)*)
      (*  (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  let hyps, bv = doit cache hyps bv in*)
      (*  let bv_base = try destr_bwcirc bv.circ *)
      (*    with CircError _ -> raise (CircError "BWCirc destr error at bvget") *)
      (*  in*)
      (*  hyps, {bv with circ = BWCirc([List.nth bv_base i])}*)
      (**)
      (*| `BvOperator ({kind = `AInit (arr_sz, bw_sz)}) :: _ ->*)
      (*  let f = match fs with*)
      (*  | [f] -> f*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  let fs = List.init arr_sz (fun i -> fapply_safe f [f_int (of_int i)]) in*)
      (*  (* List.iter (Format.eprintf "|%a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env))) fs; *)*)
      (*  let hyps, fs = List.fold_left_map (doit cache) hyps fs in*)
      (*  if not (List.for_all (fun c -> List.is_empty c.inps) fs) then*)
      (*    raise (CircError "Quantifiers/Definitions inside init lambda not supported")*)
      (*  else*)
      (*  begin try *)
      (*  hyps, {circ = BWArray(Array.of_list (List.map (fun c -> destr_bwcirc c.circ) fs)); inps=[]}*)
      (*    with CircError _ -> raise (CircError "Array elements in init should be bitstrings")*)
      (*  end*)
      (**)
      (*| `BvOperator ({kind = `Map (sz1, sz2, asz)}) :: _ -> *)
      (*  let f, a = match fs with*)
      (*  | [f; a] -> f, a*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in *)
      (*  let hyps, f = doit cache hyps f in*)
      (*  let hyps, a = doit cache hyps a in*)
      (*  hyps, circuit_map f a*)
      (**)
      (*| `BvOperator ({kind = `ASliceGet ((arr_sz, sz1), sz2)}) :: _ ->*)
      (*  let arr, i = match fs with*)
      (*  | [arr; i] -> arr, int_of_form i*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  let op = circuit_bwarray_slice_get arr_sz sz1 sz2 (to_int i) in*)
      (*  let hyps, arr = doit cache hyps arr in*)
      (*  hyps, compose op [arr]*)
      (**)
      (*| `BvOperator ({kind = `ASliceSet ((arr_sz, sz1), sz2)}) :: _ ->*)
      (*  let arr, i, bv = match fs with*)
      (*  | [arr; i; bv] -> arr, int_of_form i, bv*)
      (*  | _ -> assert false (* Should never happen, caught in EC typecheck/bindings *)*)
      (*  in*)
      (*  let op = circuit_bwarray_slice_set arr_sz sz1 sz2 (to_int i) in*)
      (*  let hyps, arr = doit cache hyps arr in*)
      (*  let hyps, bv = doit cache hyps bv in*)
      (*  hyps, compose op [arr; bv]*)
      (**)
      | _ -> begin match EcFol.op_kind (destr_op f |> fst), fs with
        | Some `Eq, [f1; f2] -> 
          let hyps, c1 = doit cache hyps f1 in
          let hyps, c2 = doit cache hyps f2 in
          hyps, circuit_eq c1 c2
          (*begin match c1.circ, c2.circ with*)
          (*| BWCirc r1, BWCirc r2 -> *)
          (*  (* assert (List.compare_lengths r1 r2 = 0); *)*)
          (*  (* Should never happen, caught in EC typecheck/bindings *)*)
          (*  hyps, {circ = BWCirc([C.bvueq r1 r2]); inps=merge_inputs c1.inps c2.inps} *)
          (*  (* FIXME: Do we allow quantifiers/definitions inside equality sides? *)*)
          (*| BWArray a1, BWArray a2 -> *)
          (*  (* assert (Array.for_all2 (fun a b -> (List.compare_lengths a b) = 0) a1 a2); *)*)
          (*  (* Should never happen, caught in EC typecheck/bindings *)*)
          (*  if not (Array.length a1 = Array.length a2) then*)
          (*    raise (CircError "Comparison between arrays of different size")*)
          (*  else*)
          (*  let rs = Array.map2 C.bvueq a1 a2 in*)
          (*  hyps, {circ = BWCirc([C.ands (Array.to_list rs)]); inps = merge_inputs c1.inps c2.inps}*)
          (*| _ -> assert false*)
          (*end*)
        (* FIXME: Remove this or the other call to op_kind (circuit_true in two places) *)
        | Some `True, [] ->
          hyps, (circuit_true :> circuit)
        | Some `False, [] ->
          hyps, (circuit_false :> circuit)
        (* recurse down into definition *)
        | _ -> 
          (* let f, fs = destr_app (apply_int_args f_) in *)
          let hyps, f_c = doit cache hyps f in
          let hyps, fcs = List.fold_left_map
            (doit cache)
            hyps fs 
          in
          hyps, circuit_compose f_c fcs
        (* | _ -> Format.eprintf "Problem at %a@." (EcPrinting.pp_form (EcPrinting.PPEnv.ofenv env)) f_; *)
          (* assert false *)
        end
      in hyps, res
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
      (*begin match lpat with*)
      (*| LSymbol (idn, ty) -> *)
      (*  let cache = update_cache cache idn vc in*)
      (*  (*let inp = cinput_of_type ~idn env ty in*)*)
      (*  (*let () = assert (match_arg inp vc.circ) in*)*)
      (*  (*let cache = Map.add idn (inp, vc) cache in*)*)
      (*  doit cache hyps f*)
      (*| LTuple symbs -> *)
      (*  let comps = if is_bwtuple tp.circ *)
      (*    then circuits_of_circuit tp*)
      (*    else raise (CircError "tuple let type error")*)
      (*  in*)
      (**)
      (*  (* Assuming types match coming from EC *)*)
      (*  let cache = List.fold_left2 (fun cache (idn, ty) c -> *)
      (*    let inp = cinput_of_type ~idn env ty in*)
      (*    Map.add idn (inp, c) cache) cache symbs comps *)
      (*  in*)
      (*  doit cache hyps f*)
      (**)
      (*| LRecord (pth, osymbs) -> raise (CircError "record types not supported")*)
      (*end*)
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
      (*let inps = List.fold_right merge_inputs (List.map (fun c -> c.inps) comps) [] in*)
      (*let comps = List.map (fun c -> destr_bwcirc c.circ) comps in*)
      (*hyps, {circ= BWTuple comps; inps}*)
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
(*let input_of_variable (env:env) (v: variable) : circuit * cinput =*)
(*  let idn = create v.v_name in*)
(*  let inp = cinput_of_type ~idn env v.v_type in*)
(*  {(circ_ident inp) with inps=[]}, inp*)

(*let pstate_of_variables ?(pstate = Map.empty) (env : env) (vars : variable list) =*)
(*  let inps = List.map (input_of_variable env) vars in*)
(*  let inpcs, inps = List.split inps in*)
(*  let inpcs = List.combine inpcs @@ List.map (fun v -> v.v_name) vars in*)
(*  let pstate = List.fold_left *)
(*    (fun pstate (inp, v) -> Map.add v inp pstate)*)
(*    pstate inpcs *)
(*  in pstate, inps*)

let vars_of_memtype ?pstate (env: env) (mt : memtype) =
  let Lmt_concrete lmt = mt in
  List.filter_map (function 
    | { ov_name = Some name; ov_type = ty } ->
      Some { v_name = name; v_type = ty; }
    | _ -> None
  ) (Option.get lmt).lmt_decl 
  

(*let pstate_of_memtype ?pstate (env: env) (mt : memtype) =*)
(*  let Lmt_concrete lmt = mt in*)
(*  let vars =*)
(*    List.filter_map (function *)
(*      | { ov_name = Some name; ov_type = ty } ->*)
(*        Some { v_name = name; v_type = ty; }*)
(*      | _ -> None*)
(*    ) (Option.get lmt).lmt_decl in*)
(*  pstate_of_variables ?pstate env vars*)

let process_instr (hyps: hyps) (mem: memory) (pstate: _) (inst: instr) : pstate =
  let env = toenv hyps in
  (* Format.eprintf "[W]Processing : %a@." (EcPrinting.pp_instr (EcPrinting.PPEnv.ofenv env)) inst; *)
  (* let start = Unix.gettimeofday () in *)
  try
    match inst.i_node with
    | Sasgn (LvVar (PVloc v, _ty), e) -> 
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
