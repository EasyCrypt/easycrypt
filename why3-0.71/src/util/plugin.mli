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

type plugin = string

exception Plugin_Not_Found of plugin * string list

val debug : Debug.flag
(** debug flag for the plugin mechanism (option "--debug
    load_plugin")
    If set [load_plugin] prints on stderr exactly which plugin are loaded.
*)

val load : ?dirs:string list -> plugin -> unit
(* [load_plugin ~dir plugin] looks in the directories [dir] for the
   plugin named [plugin]. It add the extension .cmo or .cmxs to the
   filename according to the compilation used for the main program *)

type plu =
  (* not a plugin extension *)
  | Plubad
  (* good plugin extension *)
  | Plugood
  (* good plugin extension but fail to load *)
  | Plufail of exn
  (* good plugin extension but not tested ( other kind of compilation ) *)
  | Pluother

val check_plugin : plugin -> plu
