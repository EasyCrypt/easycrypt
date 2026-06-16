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
let get_bit (b : bytes) (i : int) =
  Char.code (Bytes.get b (i / 8)) lsr (i mod 8) land 0b1 <> 0

(* -------------------------------------------------------------------- *)
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
