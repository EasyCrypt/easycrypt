(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type path = string

type xdgroots = {
  xdg_data_home   : path;
  xdg_config_home : path;
  xdg_cache_home  : path;
  xdg_data_dirs   : path list;
  xdg_config_dirs : path list;
}

val xdgroots : xdgroots

exception XdgUndefined of string

(* -------------------------------------------------------------------- *)
type mode = [`User | `System | `All]

type xdgfile =
     ?roots:xdgroots
  -> ?exists:bool
  -> appname:string
  -> mode:mode
  -> path
  -> path list

(* -------------------------------------------------------------------- *)
module Data : sig
  val user   : ?roots:xdgroots -> unit -> path
  val system : ?roots:xdgroots -> unit -> path list
  val all    : ?roots:xdgroots -> unit -> path list
  val file   : xdgfile
end

(* -------------------------------------------------------------------- *)
module Config : sig
  val user   : ?roots:xdgroots -> unit -> path
  val system : ?roots:xdgroots -> unit -> path list
  val all    : ?roots:xdgroots -> unit -> path list
  val file   : xdgfile
end

(* -------------------------------------------------------------------- *)
module Cache : sig
  val user : ?roots:xdgroots -> unit -> path
  val file : xdgfile
end
