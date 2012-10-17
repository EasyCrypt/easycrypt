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

val ft_select_kept : (Env.env,Ty.Sty.t)  Trans.flag_trans
val ft_enco_kept   : (Env.env,Task.task) Trans.flag_trans
val ft_enco_poly   : (Env.env,Task.task) Trans.flag_trans

val encoding_smt  : Env.env -> Task.task Trans.trans
val encoding_tptp : Env.env -> Task.task Trans.trans

