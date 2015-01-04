(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type at_pos = 
  | At_last
  | At_pos of int list
  | At_empty

(* -------------------------------------------------------------------- *)
type ('inv, 's) helper =
  | Helper_inv   of 'inv
  | Helper_eager of 's

type ('p, 'bad) g_inv =
  | Inv_global of 'p
  | Inv_upto   of 'bad
