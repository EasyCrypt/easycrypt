(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcPath

type node = path

type graph
type nodes

exception CycleDetected

module Graph : sig
  val empty : graph
  val add : src:node -> dst:node -> graph -> graph
  val has_path : src:node -> dst:node -> graph -> bool
  val dump : graph -> string
end

module Nodes : sig
  val empty : graph -> nodes
  val add : node -> nodes -> nodes
  val toset : nodes -> Sp.t
  val reduce : Sp.t -> graph -> Sp.t
end
