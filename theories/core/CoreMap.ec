(* The only purposes of these types and operators are to be bound to
 * the relevant SMT operators. Do not use them directly and use the
 * Map theory instead. *)

type ('a, 'b) map.

op cst ['a 'b] : 'b -> ('a, 'b) map.
op "_.[_]" ['a 'b] : ('a, 'b) map -> 'a -> 'b.
op "_.[_<-_]" ['a 'b] : ('a, 'b) map -> 'a -> 'b -> ('a, 'b) map.
