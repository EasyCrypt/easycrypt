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


module Pcre = Pcre2

open Pcre
open Parseini
open Inilexer

exception Invalid_section of string
exception Invalid_element of string
exception Missing_section of string
exception Missing_element of string
exception Ini_parse_error of (int * string)

type attribute_specification = {
  atr_name: string;
  atr_required: bool;
  atr_default: (string list) option;
  atr_validator: Pcre.regexp option;
}

type section_specification = {
  sec_name: string;
  sec_required: bool;
  sec_attributes: attribute_specification list;
}

type specification = section_specification list
  
let comment = regexp "^#.*$"

module Ordstr = 
struct
  type t = string
  let compare (x:t) (y:t) = 
    String.compare (String.lowercase_ascii x) (String.lowercase_ascii y)
end

module Strset = Set.Make(Ordstr)

let setOfList list =
  let rec dosetOfList list set = 
    match list with
	a :: tail -> dosetOfList tail (Strset.add a set)
      | []  -> set
  in
    dosetOfList list Strset.empty

let rec filterfile ?(buf=Buffer.create 500) f fd = 
  try
    let theline = input_line fd in
      if f theline then begin
	Buffer.add_string buf (theline ^ "\n");
	filterfile ~buf f fd
      end
      else
	filterfile ~buf f fd
  with End_of_file -> Buffer.contents buf

let read_inifile file fd tbl =
  let lxbuf = 
    Lexing.from_string
      (filterfile
	 (fun line -> not (Pcre.pmatch ~rex:comment line))
	 fd)
  in
    try
      let parsed_file = inifile lexini lxbuf in
	List.iter
	  (fun (section, values) ->
	     Hashtbl.add tbl section
	       (List.fold_left
		  (fun tbl (key, value) -> Hashtbl.add tbl key value;tbl)
		  (Hashtbl.create 10)
		  values))
	  parsed_file
    with Parsing.Parse_error | Failure _ ->
      raise (Ini_parse_error (lxbuf.Lexing.lex_curr_p.Lexing.pos_lnum, file))

let write_inifile fd tbl = 
  Hashtbl.iter
    (fun k v ->
       output_string fd "[";output_string fd k;output_string fd "]\n";
       (Hashtbl.iter
	  (fun k v ->
	     output_string fd k;output_string fd " = ";output_string fd v;
	     output_string fd "\n") v);
       output_string fd "\n")
    tbl

class inifile ?(spec=[]) file =
object (self)
  val file = file
  val data = Hashtbl.create 50

  initializer 
  let inch = open_in file in
    (try read_inifile file inch data
     with exn -> close_in inch;raise exn);
    close_in inch;
    self#validate

  method private validate = 
    match spec with
	[] -> ()
      | spec ->
	  List.iter
	    (fun {sec_name=name;sec_required=required;
		  sec_attributes=attrs} ->
	       try
		 let sec = 
		   try Hashtbl.find data name
		   with Not_found -> raise (Missing_section name)
		 in
		   List.iter
		     (fun {atr_name=name;atr_required=req;
			   atr_default=def;atr_validator=validator} ->
			try
			  let attr_val = 
			    try Hashtbl.find sec name
			    with Not_found -> raise (Missing_element name)
			  in
			    (match validator with
				 Some rex -> 
				   if not (Pcre.pmatch ~rex:rex attr_val) then
				     raise 
				       (Invalid_element 
					  (name ^ ": validation failed"))
			       | None -> ())
			with Missing_element elt ->
			  if req then raise (Missing_element elt)
			  else match def with
			      Some def -> List.iter (Hashtbl.add sec name) def
			    | None -> ())
		     attrs
	       with Missing_section s -> 
		 if required then raise (Missing_section s))
	    spec

  method getval sec elt =
    try Hashtbl.find 
      (try (Hashtbl.find data sec)
       with Not_found -> raise (Invalid_section sec))
      elt
    with Not_found -> raise (Invalid_element elt)

  method getaval sec elt =
    try Hashtbl.find_all
      (try (Hashtbl.find data sec)
       with Not_found -> raise (Invalid_section sec))
      elt
    with Not_found -> raise (Invalid_element elt)

  method setval sec elt v =
    (Hashtbl.add 
       (try Hashtbl.find data sec
	with Not_found ->
	  let h = Hashtbl.create 10 in
	    Hashtbl.add data sec h;h)
       elt v);
    try self#validate
    with exn -> Hashtbl.remove data elt;raise exn

  method delval sec elt =
    let valu = 
      try
	Some
	  (Hashtbl.find
	     (try Hashtbl.find data sec
	      with Not_found -> raise (Invalid_section sec))
	     elt)
      with Not_found -> None
    in
      match valu with
	  Some v ->
	    ((Hashtbl.remove
	       (try Hashtbl.find data sec
		with Not_found -> raise (Invalid_section sec))
	       elt);
	     try self#validate
	     with exn -> 
	       (Hashtbl.add
		  (try Hashtbl.find data sec
		   with Not_found -> raise (Invalid_section sec))
		 elt v);
	       raise exn)
	| None -> ()


  method sects =
    (Hashtbl.fold
       (fun k _v keys -> k :: keys)
       data [])

  method iter func sec =
    (Hashtbl.iter func 
       (try Hashtbl.find data sec
	with Not_found -> raise (Invalid_section sec)))

  method attrs sec =    
    (Strset.elements
       (setOfList
	  (Hashtbl.fold
	     (fun k _v attrs -> k :: attrs)
	     (try Hashtbl.find data sec
	      with Not_found -> raise (Invalid_section sec))
	     [])))

  method save ?(file = file) () = 
    let outch = open_out file in      
      write_inifile outch data;
      flush outch;
end

let readdir path =
  let dir = Unix.handle_unix_error Unix.opendir path in
  let rec do_read dir =
    try
      let current = Unix.readdir dir in
	current :: (do_read dir)
    with End_of_file -> []
  in
  let lst = do_read dir in
    Unix.closedir dir;
    lst

let fold func path initial =
  let check_file path = 
    match 
      (path, 
       (try (Unix.stat path).Unix.st_kind 
	with Unix.Unix_error (_,_,_) -> Unix.S_DIR)) 
    with
	(_name, Unix.S_REG) when 
	  (Pcre.pmatch ~rex:(Pcre.regexp "^.*\\.ini$") path) -> 
	    true
      | _ -> false
  in
    (List.fold_left
       func
       initial
       (List.rev_map
	  (fun x -> new inifile x)
	  (List.filter
	     check_file
	     (List.rev_map
		(fun p -> (path ^ "/" ^ p))
		(readdir path)))))
