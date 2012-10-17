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

(** Rc file management *)

(** {2 Exception} *)

type rc_value =
  | RCint of int
  | RCbool of bool
  | RCfloat of float
  | RCstring of string
  | RCident of string

(* exception SyntaxError *)
exception ExtraParameters of string
(** [ExtraParameters name] One section of name [name] has two many
    parameters : more than one if [name] is a family, more than none
    if [name] is a section *)

exception MissingParameters of string
(** [MissingParameters name] One section of a family [name] has no
    parameters *)

(* exception UnknownSection of string *)
exception UnknownField of string
(** [UnknownField key] The key [key] appeared in a section but is not
    expected there *)
(* exception MissingSection of string *)
exception MissingField of string
(** [MissingField key] The field [key] is required but not given *)
exception DuplicateSection of string
(** [DuplicateSection name] section [name] appears more than once *)
exception DuplicateField of string * rc_value * rc_value
(** [DuplicateField key] key [key] appears more than once *)
exception StringExpected of string * rc_value
(** [StringExpected key value] string expected *)
(* exception IdentExpected of string * rc_value *)
(* (\** [IdentExpected key value] string expected *\) *)
exception IntExpected of string * rc_value
(** [IntExpected key value] int expected *)
exception BoolExpected of string * rc_value
(** [BoolExpected key value] bool expected *)


(** {2 RC API} *)


type t (** Rc parsed file *)
type section (** section in rc file *)
type family  = (string * section) list (** A family in rc files *)

val empty : t (** An empty Rc *)
val empty_section : section (** An empty section *)

val get_section : t -> string -> section option
(** [get_section rc name]
    @return None if the section is not in the rc file
    @raise DuplicateSection if multiple section has the name [name]
    @raise ExtraParameters if [name] is a family in [rc] instead of a section
*)

val get_family  : t -> string -> family
(** [get_family rc name] return all the sections of the family [name]
    in [rc]
    @raise MissingParameters if [name] correspond also too a section in [rc]
 *)

val set_section : t -> string -> section -> t
(** [set_section rc name section] add a section [section] with name [name] in
    [rc]. Remove former section [name] if present in [rc] *)

val set_family  : t -> string -> family  -> t
(** [set_family rc name family] add all the section in [family] using
    the associated [string] as argument of the family [name] in the rc
    file [rc]. Remove all the former sections of family [name] if
    present in [rc] *)

val get_int  : ?default:int      -> section -> string -> int
(** [get_int ~default section key] one key to one value

    @raise Bad_value_type if the value associated to [key] is not of type
    {!int}

    @raise Key_not_found if default is not given and no value is
    associated to [key]

    @raise Multiple_value if the key appears multiple time.
*)

val get_into : section -> string -> int option

val get_intl : ?default:int list -> section -> string -> int list
(** [get_intl ~default section key] one key to many value

    @raise Bad_value_type if the value associated to [key] is not of
    type {!int}

    @raise MissingField if default is not given and no values are
    associated to [key]
*)

val set_int :?default:int -> section -> string -> int -> section
(** [set_int ?default section key value] add the association [key] to [value]
    in the section if value is not default.
    Remove all former associations with this [key]
*)

val set_intl : ?default:int list -> section -> string -> int list -> section
(** [set_int ?default section key lvalue] add the associations [key] to all the
    [lvalue] in the section if value is not default.
    Remove all former associations with this [key]
*)

val get_bool  : ?default:bool       -> section -> string -> bool
(** Same as {!get_int} but on bool *)

val get_booll  : ?default:bool list -> section -> string -> bool list
(** Same as {!get_intl} but on bool *)

val get_boolo : section -> string -> bool option

val set_bool : ?default:bool -> section -> string -> bool -> section
(** Same as {!set_int} but on bool *)

val set_booll : ?default:bool list -> section -> string -> bool list -> section
(** Same as {!set_intl} but on bool *)


val get_string  : ?default:string       -> section -> string -> string
(** Same as {!get_int} but on string *)

val get_stringl  : ?default:string list -> section -> string -> string list
(** Same as {!get_intl} but on string *)

val get_stringo : section -> string -> string option

val set_string : ?default:string -> section -> string -> string -> section
(** Same as {!set_int} but on string *)

val set_stringl : ?default:string list ->
  section -> string -> string list -> section
(** Same as {!set_intl} but on string *)

(* val ident  : ?default:string      -> section -> string -> string *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *)
(*       raise Multiple_value *)
(*   *\) *)

(* val identl : ?default:string list -> section -> string -> string list *)
(*   (\** raise Bad_value_type *)
(*       raise Key_not_found *\) *)

(* val set_ident : section -> string -> string -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

(* val set_identl : section -> string -> string list -> section *)
(*   (\** raise Yet_defined_key *)
(*       raise Bad_value_type *)
(*   *\) *)

val check_exhaustive : section -> Util.Sstr.t -> unit
(** [check_exhaustive section keys] check that only the keys in [keys]
    appear inside the section [section]

    @raise UnknownField if it is not the case
*)

exception CannotOpen of string * string
exception SyntaxErrorFile of string * string

val from_channel : in_channel -> t
(** [from_channel cin] returns the Rc of the input channel [cin]
    @raise SyntaxErrorFile in case of incorrect syntax
    @raise ExtraParameters if a section header has more than one argument
*)

val from_file : string -> t
(** [from_file filename] returns the Rc of the file [filename]
    @raise CannotOpen is [filename] does not exist
    @raise SyntaxErrorFile in case of incorrect syntax
    @raise ExtraParameters if a section header has more than one argument
*)

val to_formatter : Format.formatter -> t -> unit
  (** [to_formatter fmt rc] writes the Rc [rc] to the formatter [fmt] *)

val to_channel : out_channel -> t -> unit
  (** [to_channel cout rc] writes the Rc [rc] to the output channel [out] *)

val to_file : string -> t -> unit
  (** [to_file filename rc] writes the Rc [rc] to the file [filename] *)

val get_home_dir : unit -> string
  (** [get_home_dir ()] returns the home dir of the user *)


