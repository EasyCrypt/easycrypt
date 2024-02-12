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
type reg = node list
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
let get_bit (b : bytes) (i : int) =
  Char.code (Bytes.get b (i / 8)) lsr (i mod 8) land 0b1 <> 0

(* -------------------------------------------------------------------- *)
let env_of_regs (rs : bytes list) =
  let rs = Array.of_list rs in
  fun ((n, i) : var) -> get_bit rs.(n) i

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

  List.iteri push (List.map (deps_ ()) r);
  !out
    |> List.rev_map (fun (r, vs) ->
         let vs =
           Set.fold
             (fun v vs -> VarRange.push vs v)
             vs VarRange.empty
         in (r, vs)
       )
    |> List.sort (fun (r1, _) (r2, _) -> compare r1 r2)
