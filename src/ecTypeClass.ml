(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath

(* -------------------------------------------------------------------- *)
type graph = {
  tcg_nodes   : Sp.t Mp.t;
  tcg_closure : Sp.t Mp.t;
}

type nodes = {
  tcn_graph : graph;
  tcn_nodes : Sp.t;
}

type node = EcPath.path

exception CycleDetected

(* -------------------------------------------------------------------- *)
module Graph = struct
  let empty : graph = {
    tcg_nodes   = Mp.empty;
    tcg_closure = Mp.empty;
  }

  let dump gr =
    Printf.sprintf "%s\n"
      (String.concat "\n"
         (List.map
            (fun (p, ps) -> Printf.sprintf "%s -> %s"
              (EcPath.tostring p)
              (String.concat ", " (List.map EcPath.tostring (Sp.elements ps))))
            (Mp.bindings  gr.tcg_nodes)))

  let has_path ~src ~dst g =
    if EcPath.p_equal src dst then
      true
    else
      match Mp.find_opt src g.tcg_closure with
      | None -> false
      | Some m -> Mp.mem dst m

  let add ~src ~dst g =
    if has_path dst src g then
      raise CycleDetected;

    match Mp.find_opt src g.tcg_nodes with
    | Some m when Mp.mem dst m -> g
    | _ ->
      let up_node m = Sp.add dst (odfl Sp.empty m)
      and up_clos m =
        Sp.union
          (odfl Sp.empty (Mp.find_opt dst g.tcg_closure))
          (Sp.add dst (odfl Sp.empty m))
      in
        { g with
            tcg_nodes   = Mp.change (some -| up_node) src g.tcg_nodes;
            tcg_closure = Mp.change (some -| up_clos) src g.tcg_closure; }
end

(* -------------------------------------------------------------------- *)
module Nodes = struct
  let empty g = {
    tcn_graph = g;
    tcn_nodes = Sp.empty;
  }

  let add n nodes =
    let module E = struct exception Discard end in

    try
      let aout =
        Sp.filter
          (fun p ->
             if Graph.has_path p n nodes.tcn_graph then raise E.Discard;
             not (Graph.has_path n p nodes.tcn_graph))
          nodes.tcn_nodes
      in
        { nodes with tcn_nodes = Sp.add n aout }
    with E.Discard -> nodes

  let toset nodes = nodes.tcn_nodes

  let reduce set g =
    toset (Sp.fold add set (empty g))
end
