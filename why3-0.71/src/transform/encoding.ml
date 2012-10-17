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

open Util
open Ident
open Ty
open Term
open Decl
open Theory
open Task
open Trans

let meta_select_kept = register_meta_excl "select_kept" [MTstring]
let meta_enco_kept   = register_meta_excl "enco_kept"   [MTstring]
let meta_enco_poly   = register_meta_excl "enco_poly"   [MTstring]

let def_enco_select_smt  = "none"
let def_enco_kept_smt    = "twin"
let def_enco_poly_smt    = "decorate"

let def_enco_select_tptp = "none"
let def_enco_kept_tptp   = "twin"
let def_enco_poly_tptp   = "decorate"

let ft_select_kept = ((Hashtbl.create 17) : (Env.env,Sty.t) Trans.flag_trans)
let ft_enco_kept   = ((Hashtbl.create 17) : (Env.env,task)  Trans.flag_trans)
let ft_enco_poly   = ((Hashtbl.create 17) : (Env.env,task)  Trans.flag_trans)

let select_kept def env =
  let select = Trans.on_flag meta_select_kept ft_select_kept def env in
  let trans task =
    let add ty acc = create_meta Libencoding.meta_kept [MAty ty] :: acc in
    let decls = Sty.fold add (Trans.apply select task) [] in
    Trans.apply (Trans.add_tdecls decls) task
  in
  Trans.store trans

let encoding_smt env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_kept def_enco_select_smt env;
  Trans.print_meta Libencoding.debug Libencoding.meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_smt env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_smt env]

let encoding_tptp env = Trans.seq [
  Libencoding.monomorphise_goal;
  select_kept def_enco_select_tptp env;
  Trans.print_meta Libencoding.debug Libencoding.meta_kept;
  Trans.on_flag meta_enco_kept ft_enco_kept def_enco_kept_tptp env;
  Trans.on_flag meta_enco_poly ft_enco_poly def_enco_poly_tptp env;
  Protect_enumeration.protect_enumeration]

let () = register_env_transform "encoding_smt" encoding_smt
let () = register_env_transform "encoding_tptp" encoding_tptp

