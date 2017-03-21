(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

type ('a,'b) map.

op "_.[_]" ['a 'b]  : ('a, 'b) map -> 'a -> 'b.
op "_.[_<-_]": ('a, 'b) map -> 'a -> 'b -> ('a, 'b) map.

