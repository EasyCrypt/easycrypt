(* -------------------------------------------------------------------- *)
(* And-Inverter Graphs: hash-consed boolean circuits. A [node] is a
   shared, structurally-unique gate; [neg] points to its complement and
   the sign of [id] gives the polarity (so negation is free). *)
type name = int

type var = name * int

(* [node] is private: nodes are hash-consed, so the only way to build one
   is through the smart constructors below (which preserve the [id]/[neg]
   sharing invariant). Fields stay readable and the type matchable. *)
type node_r =
  | False
  | Input of var
  | And   of node * node

and node = private {
  gate : node_r;
  id   : int;
  neg  : node;
}

(* -------------------------------------------------------------------- *)
(* Leaves and constants. *)
val false_   : node
val true_    : node
val constant : bool -> node
val input    : var -> node

(* -------------------------------------------------------------------- *)
(* Boolean combinators (structure-sharing, with constant folding). *)
val neg  : node -> node
val and_ : node -> node -> node
val nand : node -> node -> node
val or_  : node -> node -> node
val xor  : node -> node -> node
val xnor : node -> node -> node

(* -------------------------------------------------------------------- *)
(* [map env] rewrites the inputs of a node, [env] giving the replacement
   node for an input (or [None] to keep it). *)
val map  : (var -> node option) -> node -> node

(* -------------------------------------------------------------------- *)
(* [get_bit b i] is bit [i] (little-endian) of the byte buffer [b]. *)
val get_bit : bytes -> int -> bool

(* [eval env n] evaluates the AIG [n] under the input assignment [env]. *)
val eval : (var -> bool) -> node -> bool

(* -------------------------------------------------------------------- *)
val pp_node :
  ?input_namer:(int -> string) -> Format.formatter -> node -> unit

(* -------------------------------------------------------------------- *)
(* Clears the global hash-consing table. *)
module HCons : sig
  val clear : unit -> unit
end
