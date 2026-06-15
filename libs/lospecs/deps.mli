(* -------------------------------------------------------------------- *)
(* Bit-level dependency analysis over AIGs: for each output bit, which
   bits of which inputs it depends on. *)

(* [tdeps] maps an input variable [i] to the set of its bits [j] that a
   given output bit depends on. Exposed concretely: consumers manipulate
   it as a plain map. *)
type tdeps = (int, int Set.t) Map.t

(* -------------------------------------------------------------------- *)
(* [dep n] / [deps r] are the dependencies of a node / of each output bit
   of a register. *)
val dep  : Aig.node -> tdeps
val deps : Aig.reg -> tdeps array

(* [merge_deps d1 d2] is the pointwise union of [d1] and [d2]: each input
   variable maps to the union of its bit-sets in the two. Use it to pool
   the dependencies of several output bits (e.g. into one block). *)
val merge_deps : tdeps -> tdeps -> tdeps

(* [realign_inputs ?renamings n] rewrites [n] so each input's used bits
   start at 0, returning the rewritten node and the per-input [(lo, hi)]
   shift that was applied. *)
val realign_inputs :
     ?renamings:(int -> int option)
  -> Aig.node
  -> Aig.node * (int, int * int) Map.t
