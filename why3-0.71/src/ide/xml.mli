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


type element =
    { name : string;
      attributes : (string * string) list;
      elements : element list;
    }

type t =
    { version : string;
      encoding : string;
      doctype : string;
      dtd : string;
      content : element;
    }

exception Parse_error of string

val from_file : string -> t
  (** returns the list of XML elements from the given file.
      raise [Sys_error] if the file cannot be opened.
      raise [Parse_error] if the file does not follow XML syntax
  *)

