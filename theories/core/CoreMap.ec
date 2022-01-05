(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* The only purposes of these types and operators are to be bound to
 * the relevant SMT operators. Do not use them directly and use the
 * Map theory instead. *)

type ('a, 'b) map.

op cst ['a 'b] : 'b -> ('a, 'b) map.
op "_.[_]" ['a 'b] : ('a, 'b) map -> 'a -> 'b.
op "_.[_<-_]" ['a 'b] : ('a, 'b) map -> 'a -> 'b -> ('a, 'b) map.
