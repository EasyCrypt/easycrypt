(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps

(* -------------------------------------------------------------------- *)
type gstate = {
  mutable gs_flags   : bool Mstr.t;
}

(* -------------------------------------------------------------------- *)
let create () : gstate =
  { gs_flags = Mstr.empty; }

(* -------------------------------------------------------------------- *)
let from_flags (flags : (string * bool) list) : gstate =
  { gs_flags = Mstr.of_list flags; }

(* -------------------------------------------------------------------- *)
let getflag ?(default = false) (name : string) (g : gstate) =
  Mstr.find_def default name g.gs_flags

(* -------------------------------------------------------------------- *)
let setflag (name : string) (value : bool) (g : gstate) =
  g.gs_flags <- Mstr.add name value g.gs_flags
