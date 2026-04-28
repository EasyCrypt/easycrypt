require import AllCore.

(* Rejected: the template references slot `a' twice. *)
notation #bad (a : int) "[" a ", " a "] " = a.
