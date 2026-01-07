open Aig

module Hashtbl = Batteries.Hashtbl

(* ------------------------------------------------------------------------------- *)
(* FIXME: CHECK THIS *)
let rec inputs_of_node : _ -> Aig.var Set.t =
  let cache : (int, Aig.var Set.t) Hashtbl.t = Hashtbl.create 0 in
  
  let rec doit (n : Aig.node) : Aig.var Set.t =
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None ->
      let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn
    | Some mn -> 
      mn

  and doit_r (n : Aig.node_r) = 
    match n with
    | False -> Set.empty
    | Input v -> Set.singleton v
    | And (n1, n2) -> Set.union (doit n1) (doit n2)

  in fun n -> doit n

(* ------------------------------------------------------------------------------- *)
let inputs_of_reg (r : Aig.reg) : Aig.var Set.t =
  Array.fold_left (fun acc x -> Set.union acc (inputs_of_node x)) Set.empty r

(* tdeps : int -> int set ; dependency for a single output bit 
           i |->  {j | output depends on bit j of var i }*)
type tdeps = (int, int Set.t) Map.t
(* tdblock (n, d) = merged dependencies as above for n bits 
  aka, the tdep represents dependencies for n bits rather than 1
*)
type tdblock = (int * tdeps)


let cache : (int, tdeps) Hashtbl.t = Hashtbl.create 5003 

let reset_state : unit -> unit = fun () -> Hashtbl.reset cache

(* ==================================================================== *)
let rec dep : _ -> tdeps = 
  let cache : (int, tdeps) Hashtbl.t = Hashtbl.create 0 in

  let rec doit (n: Aig.node) : tdeps = 
    match Hashtbl.find_option cache (Int.abs n.id) with
    | None -> let mn = doit_r n.gate in
      Hashtbl.add cache (Int.abs n.id) mn;
      mn 
    | Some mn -> 
      mn

  and doit_r (n: Aig.node_r) =
    match n with
    | False -> Map.empty
    | Input (v, i) -> Map.add v (Set.add i (Set.empty)) Map.empty
    | And (n1, n2) -> Map.union_stdlib (fun k s1 s2 -> Some (Set.union s1 s2)) (doit n1) (doit n2)

  in (fun n -> 
    let res = doit n in
    Hashtbl.clear cache; 
    res)

let deps (n: reg) : tdeps array = 
  Array.map dep n 

let block_deps (d: tdeps array) : tdblock list =
  let drop_while_count (f: 'a -> bool) (l: 'a list) : int * ('a list) =
    let rec doit (n: int) (l: 'a list) = 
      match l with
      | [] -> (n, [])
      | a::l' -> if f a then doit (n+1) l' else (n, l)
    in
    let n, tl = doit 0 l in
    (n, tl)
  in
  let rec decompose (l: tdeps list) : tdblock list =
    match l with
    | [] -> []
    | h::_ -> let n, l' = 
      (drop_while_count (fun a -> Map.equal (Set.equal) h a) l) in
      (n, h)::(decompose l')
  in
  decompose (Array.to_list d)

let blocks_indep ((_,b):tdblock) ((_,d):tdblock) : bool =
  let keys = Set.intersect (Set.of_enum @@ Map.keys b) (Set.of_enum @@ Map.keys d) in
  let intersects = Set.map (fun k -> 
    let b1 = Map.find k b in
    let d1 = Map.find k d in
    (Set.cardinal @@ Set.intersect b1 d1) = 0
  ) keys in
  Set.fold (&&) intersects true

let block_list_indep (bs: tdblock list) : bool =
  let rec doit (bs: tdblock list) (acc: tdblock list) : bool =
   match bs with
   | [] -> true
   | b::bs -> List.for_all (blocks_indep b) acc && doit bs (b::acc)
  in
  doit bs []

let merge_deps (d1: tdeps) (d2: tdeps) : tdeps = 
    Map.union_stdlib (fun _ a b -> Option.some (Set.union a b)) d1 d2

let split_deps (n: int) (d: tdeps array) : tdblock list =
  assert (Array.length d mod n = 0);
  let combine (d: tdeps list) : tdeps =
    List.reduce merge_deps d
  in
  let rec aggregate (acc: tdblock list) (d: tdeps array) : tdblock list =
    match d with
    | [| |] -> acc
    | _ -> (aggregate ((n, combine (Array.head d n |> Array.to_list))::acc) (Array.tail d n))
  in
  List.rev @@ aggregate [] d

let check_dep_width ?(eq=false) (n: int) (d: tdeps) : bool =
  Map.fold (fun s acc -> let m = (Set.cardinal s) in
    if eq then
      acc && (n = m)
    else
      acc && (m <= n)
    ) d true

(* maybe optimize this? *)
let tdblock_of_tdeps (d: tdeps list) : tdblock =
  (List.length d, List.reduce merge_deps d)

(* 
  Take a list of blocks and drop all but the first block if the 
  sizes are the same and the dependecy amounts are the same
*)
let compare_dep_size (a: tdeps) (b: tdeps) : bool =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) a 0) =
  (Map.fold (fun s acc -> acc + (Set.cardinal s)) b 0)   

let compare_tdblocks ((na, da): tdblock) ((nb, db): tdblock) : bool =
  (na = nb) && compare_dep_size da db

let collapse_blocks (d: tdblock list) : tdblock option = 
  match d with
  | [] -> None
  | h::t -> 
    List.fold_left 
    (fun a b -> 
      match a with
      | None -> None
      | Some a -> if compare_tdblocks a b 
                  then Some a else None) 
    (Some h) t

(* -------------------------------------------------------------------- *)
(* Uses dependency analysis to realign inputs to start at 0             *)
(* Corresponds to taking the relevant subcircuit to this output         *)
(* Assumes that inputs are contiguous FIXME                             *)
let realign_inputs ?(renamings: (int -> int option) option) (n: node) : node * (int, int * int) Map.t = 
  let d = dep n in
  let shifts = Map.map (fun s -> 
    Set.min_elt_opt s |> Option.default 0,
    Set.max_elt_opt s |> Option.default 0
  ) d in
  let map_ = 
    match renamings with
    | Some renamings -> begin fun (v, i) ->
      let v' = renamings v |> Option.default v in
      match Map.find_opt v shifts with
      | None -> None
      | Some (k, _) -> Some (Aig.input (v', i-k))
    end
    | None -> begin fun (v, i) ->
      match Map.find_opt v shifts with
      | None -> None
      | Some (k, _) -> Some (Aig.input (v, i-k))
    end
  in
  let shifts = match renamings with
  | None -> shifts
  | Some renamings ->  
    Map.to_seq shifts |> Seq.map (fun (k, v) ->
      Option.default k (renamings k), v) |> Map.of_seq
  in
  Aig.map map_ n, shifts

let pp_dep ?(namer = string_of_int) (fmt : Format.formatter) (d: tdeps) : unit =
  let print_set fmt s = Set.iter (Format.fprintf fmt "%d ") s in
  Map.iter (fun id ints -> Format.fprintf fmt "%s: %a@." (namer id) print_set ints) d

let pp_deps ?(namer = string_of_int) (fmt: Format.formatter) (ds: tdeps list) : unit = 
  List.iteri (fun i d -> Format.fprintf fmt "Output #%d:@.%a@." i (pp_dep ~namer) d) ds

let pp_bdep ?(start_index = 0) ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) ((n, d): tdblock) : unit =
  Format.fprintf fmt "[%d-%d]%s:@." start_index (start_index+n-1) oname;
  pp_dep ~namer fmt d

let pp_bdeps ?(oname="") ?(namer=string_of_int) (fmt: Format.formatter) (bs: tdblock list) : unit =
  List.fold_left (fun acc (n,d) -> (pp_bdep ~start_index:acc ~oname ~namer fmt (n,d)); acc + n) 0 bs |> ignore
