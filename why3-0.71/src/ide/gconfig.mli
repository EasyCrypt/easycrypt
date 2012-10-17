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

open Why3

type t =
    { mutable window_width : int;
      mutable window_height : int;
      mutable tree_width : int;
      mutable task_height : int;
      mutable time_limit : int;
      mutable mem_limit : int;
      mutable verbose : int;
      mutable max_running_processes : int;
      mutable default_editor : string;
      mutable intro_premises : bool;
      mutable show_labels : bool;
      mutable show_locs : bool;
      mutable saving_policy : int;
      mutable premise_color : string;
      mutable goal_color : string;
      mutable error_color : string;
      mutable env : Why3.Env.env;
      mutable config : Whyconf.config;
    }

val save_config : unit -> unit

val config : t

val get_main : unit -> Whyconf.main

(*****************)
(* images, icons *)
(*****************)

val why_icon : GdkPixbuf.pixbuf ref

val image_yes : GdkPixbuf.pixbuf ref

(* tree object icons *)
val image_directory : GdkPixbuf.pixbuf ref
val image_file : GdkPixbuf.pixbuf ref
val image_prover : GdkPixbuf.pixbuf ref
val image_transf : GdkPixbuf.pixbuf ref
val image_editor : GdkPixbuf.pixbuf ref
val image_replay : GdkPixbuf.pixbuf ref
val image_cancel : GdkPixbuf.pixbuf ref
val image_reload : GdkPixbuf.pixbuf ref
val image_remove : GdkPixbuf.pixbuf ref
val image_cleaning : GdkPixbuf.pixbuf ref

(* status icons *)
val image_undone : GdkPixbuf.pixbuf ref
val image_scheduled : GdkPixbuf.pixbuf ref
val image_running : GdkPixbuf.pixbuf ref
val image_valid : GdkPixbuf.pixbuf ref
val image_invalid : GdkPixbuf.pixbuf ref
val image_timeout : GdkPixbuf.pixbuf ref
val image_unknown : GdkPixbuf.pixbuf ref
val image_failure : GdkPixbuf.pixbuf ref
val image_valid_obs : GdkPixbuf.pixbuf ref
val image_invalid_obs : GdkPixbuf.pixbuf ref
val image_timeout_obs : GdkPixbuf.pixbuf ref
val image_unknown_obs : GdkPixbuf.pixbuf ref
val image_failure_obs : GdkPixbuf.pixbuf ref

(*************************)
(* miscellaneous dialogs *)
(*************************)

val show_legend_window : unit -> unit
val show_about_window : unit -> unit
val preferences : t -> unit

(*
Local Variables:
compile-command: "unset LANG; make -C ../.. bin/why3ide.byte"
End:
*)
