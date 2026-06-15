(* -------------------------------------------------------------------- *)
type name = int

(* -------------------------------------------------------------------- *)
type var = name * int

(* -------------------------------------------------------------------- *)
type node_r =
  | False
  | Input of var
  | And   of node * node

and node = {
  gate : node_r;
  id   : int;
  neg  : node;
}

(* -------------------------------------------------------------------- *)
type reg = node array

(* -------------------------------------------------------------------- *)
module HCons : sig
  val hashcons : node_r -> node

  val clear : unit -> unit
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

  let clear = fun () -> H.clear htable

  let hashcons (n : node_r) =
    let rec pos = { gate = n; id =   !tag; neg = neg; }
    and     neg = { gate = n; id = - !tag; neg = pos; } in

    let o = H.merge htable pos in

    if o == pos then incr tag; o
end

(* -------------------------------------------------------------------- *)
let rec pp_node ?(input_namer : int -> string =string_of_int) (fmt : Format.formatter) (n : node) =
  let pp_node = pp_node ~input_namer in
  match n with
  | { gate = False; id } when 0 < id ->
    Format.fprintf fmt "⊥"

  | { gate = False; } ->
    Format.fprintf fmt "⊤"

  | { gate = Input (n, i); id; } ->
    let s = input_namer n in
    Format.fprintf fmt "%s%s#%0.4x"
      (if 0 < id then "" else "¬") s i

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
