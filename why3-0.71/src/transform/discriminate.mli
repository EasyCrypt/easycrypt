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

val meta_inst   : Theory.meta
val meta_lskept : Theory.meta
val meta_lsinst : Theory.meta

module Lsmap : sig
  type t
  val empty : t
  val add : Term.lsymbol -> Ty.ty list -> Ty.ty option -> t -> t
end

val ft_select_inst   : (Env.env,Ty.Sty.t) Trans.flag_trans
val ft_select_lskept : (Env.env,Term.Sls.t) Trans.flag_trans
val ft_select_lsinst : (Env.env,Lsmap.t) Trans.flag_trans
