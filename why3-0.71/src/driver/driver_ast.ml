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

type loc = Loc.position

type qualid = loc * string list

type cloned = bool

type metarg =
  | PMAts  of qualid
  | PMAfs  of qualid
  | PMAps  of qualid
  | PMApr  of qualid
  | PMAstr of string
  | PMAint of int

type th_rule =
  | Rprelude  of string
  | Rsyntaxts of cloned * qualid * string
  | Rsyntaxfs of cloned * qualid * string
  | Rsyntaxps of cloned * qualid * string
  | Rremovepr of cloned * qualid
  | Rmeta     of cloned * string * metarg list

type theory_rules = {
  thr_name  : qualid;
  thr_rules : (loc * th_rule) list;
}

type global =
  | Prelude of string
  | Printer of string
  | RegexpValid of string
  | RegexpInvalid of string
  | RegexpTimeout of string
  | RegexpUnknown of string * string
  | RegexpFailure of string * string
  | TimeRegexp of string
  | ExitCodeValid of int
  | ExitCodeInvalid of int
  | ExitCodeTimeout of int
  | ExitCodeUnknown of int * string
  | ExitCodeFailure of int * string
  | Filename of string
  | Transform of string
  | Plugin of (string * string)

type file = {
  f_global : (loc * global) list;
  f_rules  : theory_rules list;
}

