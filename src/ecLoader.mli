(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type idx_t
type ecloader

type kind = [`Ec | `EcA]

(* -------------------------------------------------------------------- *)
type namespace = [ `System | `Named of string ]

(* -------------------------------------------------------------------- *)
val create  : unit -> ecloader
val aslist  : ecloader -> ((namespace option * string) * idx_t) list
val dup     : ecloader -> ecloader
val forsys  : ecloader -> ecloader
val addidir : ?namespace:namespace -> ?recursive:bool -> string -> ecloader -> unit
val locate  : ?namespaces:(namespace option) list -> string -> ecloader -> (namespace option * string * kind) option
