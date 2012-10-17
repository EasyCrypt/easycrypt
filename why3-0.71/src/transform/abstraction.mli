(**************************************************************************)
(*                                                                        *)
(*  Copyright (C) 2010-2011                                               *)
(*    François Bobot                                                      *)
(*    Jean-Christophe Filliâtre                                           *)
(*    Claude Marché                                                       *)
(*    Guillaume Melquiond                                                 *)
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




val abstraction : (Term.lsymbol -> bool) -> Task.task Trans.trans
(** [abstract keep t] applies variable abstraction of the task [t],
    that is replaces subterms or subformulas headed by a logic symbol
    f that do not satisfies [keep f] into a fresh variable.

    Notice that the numeric constants are always kept

    Example (approximate syntax):

    [abstraction (fun f -> List.mem f ["+";"-"]) "goal x*x+y*y = 1"]
    returns ["logic abs1 : int; logic abs2 : int; goal abs1+abs2 = 1"]

*)
