(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type exn_printer = Format.formatter -> exn -> unit

val register    : exn_printer -> unit
val exn_printer : exn_printer
val tostring    : exn -> string
