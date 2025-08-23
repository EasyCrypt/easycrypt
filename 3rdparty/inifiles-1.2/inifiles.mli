(* A small library to read and write .ini files

   Copyright (C) 2004 Eric Stokes, and The California State University
   at Northridge

   This library is free software; you can redistribute it and/or               
   modify it under the terms of the GNU Lesser General Public                  
   License as published by the Free Software Foundation; either                
   version 2.1 of the License, or (at your option) any later version.          
   
   This library is distributed in the hope that it will be useful,             
   but WITHOUT ANY WARRANTY; without even the implied warranty of              
   MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.  See the GNU           
   Lesser General Public License for more details.                             
   
   You should have received a copy of the GNU Lesser General Public            
   License along with this library; if not, write to the Free Software         
   Foundation, Inc., 59 Temple Place, Suite 330, Boston, MA  02111-1307  USA   
*)


(** This library reads ini format property files *)

(** raised if you ask for a section which doesn't exist *)
exception Invalid_section of string

(** raised if you ask for an element (attribute) which doesn't exist,
    or the element fails to match the validation regex *)
exception Invalid_element of string

(** raised if a required section is not specified in the config file *)
exception Missing_section of string

(** raised if a required element is not specified in the config file *)
exception Missing_element of string

(** raised if there is a parse error in the ini file it will contain the
    line number and the name of the file in which the error happened *)
exception Ini_parse_error of (int * string)

(** The type of an attribute/element specification *)
type attribute_specification = {
  atr_name: string;
  atr_required: bool;
  atr_default: (string list) option;
  atr_validator: Pcre2.regexp option;
}

(** The type of a section specification *)
type section_specification = {
  sec_name: string;
  sec_required: bool;
  sec_attributes: attribute_specification list;
}

(** The type of a secification *)
type specification = section_specification list

(** send the name of an ini file to the constructor the file must
    exist, but can be empty *)
class inifile : ?spec:specification -> string ->
object
  (** get a value from the config object raise Invalid_section, or
      invalid_element on error.  getval section element *)
  method getval : string -> string -> string

  (** get a value from the config object. return a list of all the
      objects bindings. If the key is listed on more than one line it
      will get n bindings, where n is the number of lines it is
      mentioned on.  raise Invalid_section, or invalid_element on error.
      getaval section element *)
  method getaval : string -> string -> string list

  (** set a value in the config create a new section, and or element
      if necessary.  setval section element *)
  method setval : string -> string -> string -> unit

  (** delete the topmost binding (the one returned by getval) from the
      section sec. Possibly exposeing another binding.  raise
      Invalid_section on error.  delval sec elt *)
  method delval : string -> string -> unit

  (** save the changes you have made
      optionally save to a different file *)
  method save : ?file:string -> unit -> unit

  (** iterates across a section. passes all key valu pairs to f
      exactly once.*)
  method iter : (string -> string -> unit) -> string -> unit

  (** returns a list of all sections in the file *)
  method sects : string list

  (** return all the attibutes of a section *)
  method attrs : string -> string list
end

(** Executes a fold left across a directory of ini files
    (skips files which do not end with .ini). fold f path a 
    computes (f ... (f (f file1 a) file2) fileN) *)
val fold: ('a -> inifile -> 'a) -> string -> 'a -> 'a
