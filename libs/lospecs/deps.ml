(* -------------------------------------------------------------------- *)
open Aig

module Hashtbl = Batteries.Hashtbl

(* -------------------------------------------------------------------- *)
(* tdeps : int -> int set ; dependency for a single output bit          *)
(*         i  |->  { j | output depends on bit j of var i }             *)
type tdeps = (int, int Set.t) Map.t

(* -------------------------------------------------------------------- *)
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
    | And (n1, n2) ->
        Map.union_stdlib
          (fun k s1 s2 -> Some (Set.union s1 s2))
          (doit n1)
          (doit n2)

  in
    fun (node : node) -> 
      let aout = doit node in
      Hashtbl.clear cache; 
      aout

(* -------------------------------------------------------------------- *)
let deps (n: reg) : tdeps array = 
  Array.map dep n 

(* -------------------------------------------------------------------- *)
let merge_deps (d1: tdeps) (d2: tdeps) : tdeps = 
  Map.union_stdlib (fun _ a b -> Option.some (Set.union a b)) d1 d2

(* -------------------------------------------------------------------- *)
let realign_inputs
  ?(renamings : (int -> int option) option)
   (node : node)
  : node * (int, int * int) Map.t
=
  let dependencies = dep node in

  let shifts = Map.map (fun s -> 
    Set.min_elt_opt s |> Option.default 0,
    Set.max_elt_opt s |> Option.default 0
  ) dependencies in

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

  let shifts =
    match renamings with
    | None -> shifts
    | Some renamings ->  
      Map.to_seq shifts |> Seq.map (fun (k, v) ->
        Option.default k (renamings k), v) |> Map.of_seq
  in

  Aig.map map_ node, shifts
