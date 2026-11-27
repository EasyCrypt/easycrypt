(* A theory that exists only in this subdirectory. It is reachable from
   fixtures/sub/entry.ec, its neighbour, and must be reachable from
   nowhere else: a LOAD of a file in another directory has to leave the
   include path with no memory of this one. *)
op neighbour : int = 3.
