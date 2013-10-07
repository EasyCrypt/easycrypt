(* -------------------------------------------------------------------- *)
open EcPath

type node  = path

type graph
type nodes

exception CycleDetected

module Graph : sig
  val empty : graph

  val add : src:node -> dst:node -> graph -> graph

  val has_path : src:node -> dst:node -> graph -> bool
end

module Nodes : sig
  val empty : graph -> nodes

  val add : node -> nodes -> nodes

  val toset : nodes -> Sp.t

  val reduce : Sp.t -> graph -> Sp.t
end
