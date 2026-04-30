(* Unit tests for the `expect "..." by print ...` command. *)

require import Int.

type point = { x : int; y : int; }.

op foo : int = 1.
op bar (n : int) : int = n + 1.

axiom foo_pos : 0 < foo.

(* nullary op *)
expect "op foo : int = 1." by print op foo.

(* op with arguments *)
expect "op bar (n : int) : int = n + 1." by print op bar.

(* record type *)
expect "type point = { x: int; y: int; }." by print type point.

(* axiom *)
expect "axiom foo_pos: 0 < foo." by print axiom foo_pos.

(* multi-line string literal with leading/trailing whitespace is
   tolerated (String.trim-based comparison) *)
expect "

    op foo : int = 1.

  " by print op foo.
