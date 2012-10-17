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

(** Proof Tasks, Cloning and Meta History *)

open Util
open Ident
open Ty
open Term
open Decl
open Theory

type tdecl_set = private {
  tds_set : Stdecl.t;
  tds_tag : Hashweak.tag;
}

val tds_equal : tdecl_set -> tdecl_set -> bool
val tds_hash : tdecl_set -> int
val tds_empty : tdecl_set

type clone_map = tdecl_set Mid.t
type meta_map = tdecl_set Mmeta.t

(** Task *)

type task = task_hd option

and task_hd = private {
  task_decl  : tdecl;        (* last declaration *)
  task_prev  : task;         (* context *)
  task_known : known_map;    (* known identifiers *)
  task_clone : clone_map;    (* cloning history *)
  task_meta  : meta_map;     (* meta properties *)
  task_tag   : Hashweak.tag; (* unique magical tag *)
}

val task_equal : task -> task -> bool
val task_hd_equal : task_hd -> task_hd -> bool

val task_hash : task -> int
val task_hd_hash : task_hd -> int

val task_known : task -> known_map
val task_clone : task -> clone_map
val task_meta  : task -> meta_map

val find_clone_tds : task -> theory -> tdecl_set
val find_meta_tds  : task -> meta -> tdecl_set

(** {2 constructors} *)

val add_decl : task -> decl -> task
val add_tdecl : task -> tdecl -> task

val use_export : task -> theory -> task
val clone_export : task -> theory -> th_inst -> task
val add_meta : task -> meta -> meta_arg list -> task

(** {2 declaration constructors + add_decl} *)

val add_ty_decl : task -> ty_decl list -> task
val add_logic_decl : task -> logic_decl list -> task
val add_ind_decl : task -> ind_decl list -> task
val add_prop_decl : task -> prop_kind -> prsymbol -> term -> task

(** {2 utilities} *)

val split_theory : theory -> Spr.t option -> task -> task list
  (** [split_theory th s t] returns the tasks of [th] added to [t]
      that end by one of [s]. They are in the opposite order than
      in the theory *)

val bisect : (task -> bool) -> task -> task
   (** [bisect test task] return a task included in [task] which is at
       the limit of truthness of the function test. The returned task is
       included in [task] and if any declarations are removed from it the
       task doesn't verify test anymore *)

(** {2 realization utilities} *)

val used_theories : task -> theory Mid.t
  (** returns a map from theory names to theories themselves *)

val used_symbols : theory Mid.t -> theory Mid.t
  (** takes the result of [used_theories] and returns
      a map from symbol names to their theories of origin *)

val local_decls : task -> theory Mid.t -> decl list
  (** takes the result of [used_symbols] and returns
      the list of declarations that are not imported
      with those theories or derived thereof *)

(** {2 bottom-up, tail-recursive traversal functions} *)

val task_fold : ('a -> tdecl -> 'a) -> 'a -> task -> 'a
val task_iter : (tdecl -> unit) -> task -> unit

val task_tdecls : task -> tdecl list
val task_decls  : task -> decl list

val task_goal  : task -> prsymbol
val task_goal_fmla  : task -> term

(** {2 selectors} *)

val on_meta : meta -> ('a -> meta_arg list -> 'a) -> 'a -> task -> 'a
val on_theory : theory -> ('a -> symbol_map -> 'a) -> 'a -> task -> 'a

val on_meta_excl : meta -> task -> meta_arg list option
val on_used_theory : theory -> task -> bool

val on_tagged_ty : meta -> task -> Sty.t
val on_tagged_ts : meta -> task -> Sts.t
val on_tagged_ls : meta -> task -> Sls.t
val on_tagged_pr : meta -> task -> Spr.t

(* exceptions *)

exception NotTaggingMeta of meta
exception NotExclusiveMeta of meta

exception GoalNotFound
exception GoalFound
exception SkipFound
exception LemmaFound

