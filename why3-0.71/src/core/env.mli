(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Andrei Paskevich                                                    *)
(*                                                                        *)
(*  This software is free software; you can redistribute it and/or        *)
(*  modify it under the terms of the GNU Library General Public           *)
(*  License version 2.1, with the special exception on linking            *)
(*  described in file LICENSE.                                            *)
(*                                                                        *)
(*  This software is distributed in the hope that it will be useful,      *)
(*  but WITHOUT ANY WARRANTY; without even the implied warranty of        *)
(*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  *)
(*                                                                        *)
(**************************************************************************)

(** Library environment *)

type env

val env_tag : env -> Hashweak.tag

module Wenv : Hashweak.S with type key = env

(** Local type aliases and exceptions *)

type fformat = string (* format name *)
type filename = string (* file name *)
type extension = string (* file extension *)
type pathname = string list (* path in an environment *)

exception KnownFormat of fformat
exception UnknownFormat of fformat
exception UnknownExtension of extension
exception UnspecifiedFormat

exception ChannelNotFound of pathname
exception TheoryNotFound of pathname * string

(** Input formats *)

open Theory

type read_channel =
  env -> pathname -> filename -> in_channel -> theory Util.Mstr.t
(** a function of type [read_channel] parses a channel using
    its own syntax. The string argument indicates the origin of
    the stream (e.g. file name) to be used in error messages. *)

val register_format : fformat -> extension list -> read_channel -> unit
(** [register_format name extensions fn] registers a new format
    called [name], for files with extensions in the string list
    [extensions] (separating dot not included);
    [fn] is the function to perform parsing.

    @raise KnownFormat [name] if the format is already registered *)

val read_channel :
  ?format:fformat -> env -> filename -> in_channel -> theory Util.Mstr.t
(** [read_channel ?format env path file ch] returns the theories in [ch].
    When given, [format] enforces the format, otherwise we choose
    the format according to [file]'s extension. Nothing ensures
    that [ch] corresponds to the contents of [f].

    @raise UnknownFormat [format] if the format is not registered
    @raise UnknownExtension [s] if the extension [s] is not known
      to any registered parser
    @raise UnspecifiedFormat if format is not given and [file]
      has no extension *)

val read_file : ?format:fformat -> env -> filename -> theory Util.Mstr.t
(** [read_file ?format env file] returns the theories in [file].
    When given, [format] enforces the format, otherwise we choose
    the format according to [file]'s extension. *)

val list_formats : unit -> (fformat * extension list) list

(** Environment construction and utilisation *)

val create_env : filename list -> env
(** creates an environment from a "loadpath", a list of directories
    containing loadable Why3/WhyML/etc files *)

val create_env_of_loadpath : filename list -> env
(** the same as [create_env], will be removed in some future version *)

val get_loadpath : env -> filename list
(** returns the loadpath of a given environment *)

val find_channel : env -> fformat -> pathname -> filename * in_channel
(** finds an input channel in a given environment, knowing its format
    and its name (presented as a list of strings); a filename is also
    returned, to be used in logs or error messages.

    @raise ChannelNotFound [sl] if the channel [sl] was not found
    @raise UnknownFormat [f] if the format is not registered *)

val find_theory : env -> pathname -> string -> theory
(** a special case of [find_channel] that returns a particular theory,
    using the format ["why"]

    @raise TheoryNotFound if the theory was not found in a channel *)
