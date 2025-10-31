(* -------------------------------------------------------------------- *)
type name = int
[@@deriving yojson]

(* -------------------------------------------------------------------- *)
type var = name * int
[@@deriving yojson]

(* -------------------------------------------------------------------- *)
type node_r =
  | False
  | Input of var
  | And   of node * node
[@@deriving yojson]

and node = {
  gate : node_r;
  id   : int;
  neg  : node;
}
[@@deriving yojson]

(* -------------------------------------------------------------------- *)
let fresh =
  let counter = ref 0 in
  fun () -> incr counter; !counter

(* -------------------------------------------------------------------- *)
type reg = node array
[@@deriving yojson]

(* -------------------------------------------------------------------- *)
module HCons : sig
  val hashcons : node_r -> node
end = struct
  module H = Weak.Make(struct
    type t = node

    let hash (x : t) : int =
      match x.gate with
      | False ->
         Hashtbl.hash False
      | Input v ->
         Hashtbl.hash v
      | And (n1, n2) ->
         Hashtbl.hash (abs n1.id, abs n2.id)

    let equal (n1 : node) (n2 : node) =
      match n1.gate, n2.gate with
      | False, False ->
         true
      | Input v1, Input v2 ->
         v1 = v2
      | And (n1, m1), And (n2, m2) ->
         n1 == n2 && m1 == m2
      | _, _ ->
         false
  end)

  let tag = ref 1

  let htable = H.create 5003

  let hashcons (n : node_r) =
    let rec pos = { gate = n; id =   !tag; neg = neg; }
    and     neg = { gate = n; id = - !tag; neg = pos; } in

    let o = H.merge htable pos in

    if o == pos then incr tag; o
end

(* -------------------------------------------------------------------- *)
let rec pp_node (fmt : Format.formatter) (n : node) =
  match n with
  | { gate = False; id } when 0 < id ->
    Format.fprintf fmt "⊥"

  | { gate = False; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input (n, i); id; } ->
    Format.fprintf fmt "%s%d#%0.4x"
      (if 0 < id then "" else "¬") n i

  | { gate = And (n1, n2); id; } when 0 < id ->
    Format.fprintf fmt "(%a) ∧ (%a)" pp_node n1 pp_node n2

  | { gate = And (n1, n2); } ->
    Format.fprintf fmt "¬((%a) ∧ (%a))" pp_node n1 pp_node n2

(* -------------------------------------------------------------------- *)
let mk (n : node_r) : node =
  HCons.hashcons n

(* -------------------------------------------------------------------- *)
let false_ : node =
  mk False

(* -------------------------------------------------------------------- *)
let true_ : node =
  false_.neg

(* -------------------------------------------------------------------- *)
let input (i : var) : node =
  mk (Input i)

(* -------------------------------------------------------------------- *)
let constant (b : bool) : node =
  if b then true_ else false_

(* -------------------------------------------------------------------- *)
let neg (n : node) : node =
  n.neg

(* -------------------------------------------------------------------- *)
let and_ (n1 : node) (n2 : node) : node =
  match () with
  | _ when n1 == n2     -> n1
  | _ when n1 == n2.neg -> false_
  | _ when n1 == false_ -> false_
  | _ when n2 == false_ -> false_
  | _ when n1 == true_  -> n2
  | _ when n2 == true_  -> n1
  | _                   -> mk (And (n1, n2))

(* -------------------------------------------------------------------- *)
let nand (n1 : node) (n2 : node) : node =
  neg (and_ n1 n2)

(* -------------------------------------------------------------------- *)
let or_ (n1 : node) (n2 : node) : node =
  nand (neg n1) (neg n2)

(* -------------------------------------------------------------------- *)
let xor (n1 : node) (n2 : node) : node =
  let n = nand n1 n2 in nand (nand n1 n) (nand n2 n)

(* -------------------------------------------------------------------- *)
let xnor (n1 : node) (n2 : node) : node =
  neg (xor n1 n2)

(* -------------------------------------------------------------------- *)
let get_bit (b : bytes) (i : int) =
  Char.code (Bytes.get b (i / 8)) lsr (i mod 8) land 0b1 <> 0

(* -------------------------------------------------------------------- *)
let env_of_regs (rs : bytes list) =
  let rs = Array.of_list rs in
  fun ((n, i) : var) -> get_bit rs.(n) i

(* ==================================================================== *)
let map (env : var -> node option) : node -> node =
  let cache : (int, node) Hashtbl.t = Hashtbl.create 0 in

  let rec doit (n : node) : node =
    let mn =
      match Hashtbl.find_option cache (abs n.id) with
      | None ->
        let mn = doit_r n.gate in
        Hashtbl.add cache (abs n.id) mn;
        mn
      | Some mn ->
        mn
    in
      if 0 < n.id then mn else neg mn

  and doit_r (n : node_r) =
    match n with
    | False ->
      false_
    | Input v ->
      Option.default (input v) (env v)
    | And (n1, n2) ->
      and_ (doit n1) (doit n2)

  in fun (n : node) -> doit n

(* -------------------------------------------------------------------- *)
let maps (env : var -> node option) : reg -> reg =
  fun r -> Array.map (map env) r

(* ==================================================================== *)
let equivs (inputs : (var * var) list) (c1 : reg) (c2 : reg) : bool =
  let inputs = Map.of_seq (List.to_seq inputs) in
  let env (v : var) = Option.map input (Map.find_opt v inputs) in
  Array.for_all2 (==) (maps env c1) c2

(* ==================================================================== *)
let eval (env : var -> bool) =
  let cache : (int, bool) Hashtbl.t = Hashtbl.create 0 in

  let rec for_node (n : node) =
    let value =
      match Hashtbl.find_option cache (abs n.id) with
      | None ->
         let value = for_node_r n.gate in
         Hashtbl.add cache (abs n.id) value;
         value
      | Some value ->
         value

    in if 0 < n.id then value else not value

  and for_node_r (n : node_r) =
    match n with
    | False -> false
    | Input x -> env x
    | And (n1, n2) -> for_node n1 && for_node n2

  in fun (n : node) -> for_node n

(* -------------------------------------------------------------------- *)
let evals (env : var -> bool) =
  List.map (eval env)

(* -------------------------------------------------------------------- *)
let eval0 (n : node) =
  eval (fun (_ : var) -> false) n

(* ==================================================================== *)
module VarRange : sig
  type 'a t

  val empty : 'a t

  val push : 'a t -> ('a * int) -> 'a t

  val contents : 'a t -> ('a * (int * int) list) list

  val pp :
       (Format.formatter -> 'a -> unit)
    -> Format.formatter
    -> 'a t
    -> unit
end = struct
  type range = int * int

  type ranges = range list

  type 'a dep1 = 'a * ranges

  type 'a t = ('a, ranges) Map.t

  let empty : 'a t =
    Map.empty

  let rec add (rg : ranges) (v : int) =
    match rg with
    | [] ->
      [(v, v)]

      (* join two segments *)
    | (lo, hi) :: (lo', hi') :: tl when hi+1 = v && v+1 = lo' ->
      (lo, hi') :: tl

      (* add to the front of a segment *)
    | (lo, hi) :: tl when v+1 = lo ->
      (v, hi) :: tl

      (* add to the back of a segment *)
    | (lo, hi) :: tl when hi+1 = v ->
      (lo, v) :: tl

    | hd :: tl ->
      hd :: add tl v

  let push (r : 'a t) ((n, i) : 'a * int) : 'a t =
    let change (rg : ranges option) =
      Some (add (Option.default [] rg) i)
    in Map.modify_opt n change r

  let contents (r : 'a t) : ('a * ranges) list =
    Map.bindings r

  let pp
      (pp  : Format.formatter -> 'a -> unit)
      (fmt : Format.formatter)
      (r   : 'a t)
  =
    let pp_range (fmt : Format.formatter) ((lo, hi) : range) =
      if lo = hi then
        Format.fprintf fmt "%d" lo
      else
        Format.fprintf fmt "%d-%d" lo hi in

    let pp_ranges (fmt : Format.formatter) (rgs : ranges) =
      Format.fprintf fmt "%a"
        (Format.pp_print_list
           ~pp_sep:(fun fmt () -> Format.fprintf fmt ",")
           pp_range)
        rgs in

    let pp_dep1 (fmt : Format.formatter) ((v, rgs) : 'a dep1) =
      Format.fprintf fmt "%a#%a" pp v pp_ranges rgs in

    Format.fprintf fmt "%a"
      (Format.pp_print_list
         ~pp_sep:(fun fmt () -> Format.fprintf fmt "; ")
         pp_dep1)
      (Map.bindings r)
end

(* ==================================================================== *)
let deps_ () =
  let cache : (int, var Set.t) Hashtbl.t = Hashtbl.create 0 in

  let rec doit_force (n : node) =
    match n.gate with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  and doit (n : node) =
    match Hashtbl.find_option cache (abs n.id) with
    | Some value ->
      value
    | None ->
      let value = doit_force n in
      Hashtbl.add cache (abs n.id) value; value

  in fun (n : node) -> doit n

(* -------------------------------------------------------------------- *)
let deps (r : reg) =
  let out = ref [] in

  let push (hi : int) (dhi : var Set.t) =
    match !out with
    | _ when Set.is_empty dhi ->
      ()
    | ((lo, v), dlo) :: tl when v+1 = hi && not (Set.disjoint dlo dhi) ->
      out := ((lo, hi), Set.union dlo dhi) :: tl
    | _ ->
      out := ((hi, hi), dhi) :: !out in

  Array.iteri push (Array.map (deps_ ()) r);
  !out
    |> List.rev_map (fun (r, vs) ->
         let vs =
           Set.fold
             (fun v vs -> VarRange.push vs v)
             vs VarRange.empty
         in (r, vs)
       )
    |> List.sort (fun (r1, _) (r2, _) -> compare r1 r2)

exception AigerError of string

(* -------------------------------------------------------------------- *)
(* SERIALIZATION *)
(* Return map of indice renaming + list of and gates (increasing order) + (max variable index, and gate count, input gate count) *)
let aiger_preprocess ~(input_count: int) (r: reg) : (node -> int) * (node list) * (int * int * int) =
  let cache : (int, int) Hashtbl.t = Hashtbl.create 0 in
  let count_and = ref 0 in
  let and_gates = ref [] in 

  let rec doit (n: node) : unit = 
    match Hashtbl.find_option cache (abs n.id) with
    | Some v -> ()
    | None ->
        let value = doit_force n in
        Hashtbl.add cache (abs n.id) value

  and doit_force (n: node) =
    match n.gate with
    | False -> 0
    | Input (v, i) -> 64*v + i
    | And (n1, n2) -> 
        doit n1; doit n2;
        incr count_and; 
        and_gates := n::(!and_gates);
        !count_and
  in

  Array.iter doit r;
  let and_cnt = !count_and in
  let inp_cnt = input_count in
  let id_map = 
    Hashtbl.to_seq cache |> Map.of_seq
  in
  let id_map = (function 
  | { gate = False; id } -> (if 0 < id then 0 else 1)
  | { gate = And _; id } -> ((Map.find (abs id) id_map) + inp_cnt) lsl 1 + (if 0 < id then 0 else 1) 
  | { gate = Input _; id } -> (Map.find (abs id) id_map) lsl 1 + (if 0 < id then 0 else 1)
  ) in
  id_map, 
  List.sort (fun n1 n2 -> compare (id_map n1) (id_map n2)) !and_gates,
  (and_cnt + inp_cnt, and_cnt, inp_cnt) 

let aiger_serialize_int (id: int) : string =
  if not (id > 0) then raise (AigerError "serialize_int");
  let mask = 0x7f in
  let rec doit (id: int) : int list = 
    if id < 0x80 then
      [id]
    else
      ((id land mask) lor (0x80))::(doit (id lsr 7))
  in

  List.fold_left (fun acc id -> (Format.sprintf "%c" (char_of_int id)) ^ acc) "" (List.rev (doit id))

let pp_aiger_int fmt (id: int) : unit =
  Format.fprintf fmt "%s" (aiger_serialize_int id)

(* FIXME PR: Look at correction of this and after making sure it is correct   *)
(*           we can remove or do something else with the asserts              *)
(*           but they should not be triggered on a normal execution           *)
let pp_aiger_and fmt ((gid, id1, id2): int * int * int) : unit =
  if not (gid > id1 && id1 > id2) then Format.eprintf "gid : %d | id1: %d | id2: %d@." gid id1 id2;
  assert (gid > id1 && id1 > id2);
  let delta0 = gid - id1 in
  let delta1 = id1 - id2 in
  assert(delta0 > 0 && delta1 > 0);
  assert(id1 = gid - delta0);
  assert(gid - delta0 - delta1 = id2);
  Format.fprintf fmt "%a%a" pp_aiger_int (gid - id1) pp_aiger_int (id1 - id2)

(* 
   mvi -> Max Variable Index
   agc -> And    Gate Count
   igc -> Input  Gate Count
   lgc -> Latch  Gate Count
   ogc -> Output Gate Count 
*)
let write_aiger_bin 
  ~(input_count: int) 
  ?(inp_name_map : int -> string = fun (i: int) -> "inp" ^ (string_of_int i))
  oc 
  (r: reg) =
  let aiger_id_of_node, and_gates, (mvi, agc, igc) = aiger_preprocess ~input_count r in

  let ogc = Array.length r in
  let lgc = 0 in
  Printf.fprintf oc "aig %d %d %d %d %d\n" mvi igc lgc ogc agc;
  Array.iter (fun n -> Printf.fprintf oc "%d\n" (aiger_id_of_node n)) r;
  List.iter (function 
    | { gate = And (n1, n2); } as n -> 
        let id  = aiger_id_of_node n  in
        let id1 = aiger_id_of_node n1 in
        let id2 = aiger_id_of_node n2 in
        let id = id - (id land 1) in
        let id1, id2 = if id1 > id2 then id1, id2 else id2, id1 in 
        Printf.fprintf oc "%s" (Format.asprintf "%a" pp_aiger_and (id, id1, id2))
    | _ -> assert false (* Should not be triggered *)
  ) and_gates;
  for i = 0 to igc-1 do 
    Printf.fprintf oc "i%d %s@\n" i (inp_name_map i)
  done

let write_aiger_bin_temp
  ~(input_count: int)
  ?(inp_name_map: (int -> string) option)
  ?(name: string = "circuit")
  (r: reg) =
    let tf_name, tf_oc = Filename.open_temp_file ~mode:[Open_binary] name ".aig" in
    let tf_oc = BatIO.output_channel ~cleanup:true tf_oc in
    write_aiger_bin ~input_count ?inp_name_map tf_oc r;
    tf_name

(* Assumes inputs are already matched *)
let abc_check_equiv 
  ?(r1_name = "r1") 
  ?(r2_name = "r2") 
  ~(input_count: int) 
  ?(inp_name_map: (int -> string) option) 
  (r1: reg) (r2: reg) : bool = 

  let tf1_name, tf1_oc = Filename.open_temp_file ~mode:[Open_binary] r1_name ".aig" in
  let tf2_name, tf2_oc = Filename.open_temp_file ~mode:[Open_binary] r2_name ".aig" in
  Format.eprintf "Created temp files (%s) (%s)!@." tf1_name tf2_name;
  let tf1_oc = BatIO.output_channel ~cleanup:true tf1_oc in
  let tf2_oc = BatIO.output_channel ~cleanup:true tf2_oc in
  write_aiger_bin ~input_count ?inp_name_map tf1_oc r1;
  write_aiger_bin ~input_count ?inp_name_map tf2_oc r2;
  Format.eprintf "Wrote aig files!@.";
  BatIO.close_out tf1_oc; BatIO.close_out tf2_oc;
  let abc_command = Format.sprintf "cec %s %s" tf1_name tf2_name in
  Format.eprintf "Abc command: %s@." abc_command;
  let abc_output_c, abc_in = Unix.open_process "abc" in
(*   let abc_in = BatIO.output_channel ~cleanup:true abc_in in *)
  BatIO.write_string abc_in (abc_command ^ "\n");
  BatIO.close_out abc_in;
(*   let abc_output_c = BatIO.input_channel ~autoclose:true ~cleanup:true abc_output_c in *)
  (* FIXME: Get the actual output in all cases from abc *)
  let re = Str.regexp {|.*Networks are equivalent.*|} in
  Format.eprintf "Before read@.";
  let abc_output = BatIO.read_all abc_output_c in
  Format.eprintf "====== BEGIN ABC OUTPUT =====@.%s@.======= END ABC OUTPUT =====@." abc_output;
  let abc_output = String.replace_chars (function | '\n' -> "|" | c -> String.of_char c) abc_output in
  if Str.string_match re abc_output 0 then true else false
 
(* -------------------------------------------------------------------- *)
exception InvalidWire

(* -------------------------------------------------------------------- *)
(* true -> positive wire *)
let u2si (u : int) : bool * int =
  if u < 0 then raise InvalidWire;
  let s = (u land 0b1) = 0 in
  let i = u lsr 1 in  (* We divide by 2 *)
  (s, i)

(* -------------------------------------------------------------------- *)
let si2u ((b, i) : bool * int) : int =
  assert (0 <= i);
  (i lsl 1) lor (match b with true -> 0 | false -> 1)

(* -------------------------------------------------------------------- *)
exception InvalidAIG of string

(* -------------------------------------------------------------------- *)
(* Load an aig file                                                     *)
let load (inp : IO.input) : reg * (Set.String.t * string array) option =
  let parse_asuint =
    let re = Str.regexp "^[0-9]+$" in

    let doit (x : string) =
      if not (Str.string_match re x 0) then
        raise (InvalidAIG ("not a valid uint: " ^ x));
      int_of_string x           (* FIXME: overflow *)
    in fun x -> doit x in 

  let header = String.trim (IO.read_line inp) in
  let header = Str.split (Str.regexp "[ \t]+") header in
  let header = Array.of_list header in

  if Array.length header <> 6 || header.(0) <> "aig" then
    raise (InvalidAIG "invalid header");

  let c_m = parse_asuint header.(1) in  (* maximum variable index *)
  let c_i = parse_asuint header.(2) in  (* number of inputs *)
  let c_l = parse_asuint header.(3) in  (* number of latches *)
  let c_o = parse_asuint header.(4) in  (* number of outputs *)
  let c_a = parse_asuint header.(5) in  (* number of AND gates *)

  (* We have c_l = 0 so /\ c_m = c_i + c_l + c_a 
   *
   * Hence: c_m = c_i + c_a
   *)

  if c_m <> c_i + c_l + c_a || c_l <> 0 then
    raise (InvalidAIG "invalid header (sum)");

  let outputs = ref [] in

  (* Reading outputs *)
  for _ = 1 to c_o do
    let output = String.trim (IO.read_line inp) in
    let (_, u) as output = u2si (parse_asuint output) in

    if not (0 <= u && u <= c_m) then
      raise (InvalidAIG "invalid output");

    outputs := output :: !outputs
  done;

  let outputs = Array.of_list (List.rev !outputs) in

  (* Reading arguments of AND gate *)
  let read_uint () =
    let exception Done in

    let i, o = ref 0, ref 0 in
    try
      while true do
        assert (!o < 4);
        let d = IO.read_byte inp in
        i := !i lor ((d land 0x7f) lsl (7 * !o));
        o := !o + 1;
        if (d land 0x80) = 0 then
          raise Done
      done;
      assert false
    with Done -> !i
  in


  let gates = List.fold_left (fun map -> function
    | 0 ->
       Map.add 0 false_ map

    | i when 0 < i && i <= c_i ->
       Map.add i (input (0, i-1)) map

    | i when c_i < i && i <= c_i + c_a ->
       let delta0 = read_uint () in
       let delta1 = read_uint () in

       if delta0 = 0 then
         raise (InvalidAIG "invalid delta0");

       (* delta0 = lhs - rhs0, delta1 = rhs0 - rhs1 *)

       let lhs  = 2 * i in
       let rhs0_ = lhs - delta0 in
       let rhs1_ = rhs0_ - delta1 in

       if lhs = c_i*2 + 2 then
         Format.eprintf "Lhs: %d | Rhs0: %d | Rhs1: %d@." lhs rhs0_ rhs1_;

       let (b1, u1) = try 
         u2si rhs0_
       with InvalidWire ->
         Format.eprintf "Invalid wire for rhs0 for params: lhs: %d | rhs0: %d | rhs1: %d@." lhs rhs0_ rhs1_; assert false
       in
       let (b2, u2) = try 
         u2si rhs1_ 
       with InvalidWire ->
         Format.eprintf "Invalid wire for rhs1 for params: lhs: %d | rhs0: %d | rhs1: %d@." lhs rhs0_ rhs1_; assert false
       in

       let n1 = Map.find u1 map in
       let n1 = if b1 then n1 else n1.neg in
       let n2 = Map.find u2 map in
       let n2 = if b2 then n2 else n2.neg in

       if not (u1 <= c_m && u2 <= c_m) then
         raise (InvalidAIG "invalid delta1");

       Map.add i (and_ n1 n2) map

    | _ ->
       assert false
  ) Map.empty (List.init (c_i + c_a + 1) (fun i -> i)) in

  (* Reading annotations *)
  let ainputs = Array.make c_i None in

  begin try
    while true do
      let exception Continue in

      try
        let line = String.trim (IO.read_line inp) in

        if line = "" then
          raise Continue;
        if line = "c" then
          raise IO.No_more_input;

        if not (
          Str.string_match
            (Str.regexp "^i\\([0-9]+\\)[ \t]+\\(.*\\)$")
            line 0
        ) then raise (InvalidAIG ("invalid annotation: " ^ line));

        let s = Str.matched_group 2 line in
        let i = parse_asuint (Str.matched_group 1 line) in

        if not (i < c_i) then
          raise (InvalidAIG "invalid annotation (index)");

        if Option.is_some ainputs.(i) then
          raise (InvalidAIG "invalid annotation (dup. index)");

        ainputs.(i) <- Some s

      with Continue -> ()
    done

  with IO.No_more_input -> () end;

  let ainputs =
    if Array.for_all Option.is_none ainputs then
      None
    else if Array.exists Option.is_none ainputs then
      raise (InvalidAIG "invalid annotation (partial)")
    else
      let ainputs = Array.map Option.get ainputs in
      let keys = Set.String.of_array ainputs in

      if Set.String.cardinal keys <> Array.length ainputs then
        raise (InvalidAIG "invalid annotation (dup)");
      Some (keys, ainputs)
  in

  (* Construct network *)
  Array.map (fun (b, i) ->
    if b then (Map.find i gates).neg else Map.find i gates
  ) outputs, ainputs
