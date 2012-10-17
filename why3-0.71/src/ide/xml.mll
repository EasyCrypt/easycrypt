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


{

  open Lexing

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

  let buf = Buffer.create 17

  let rec pop_all group_stack element_stack =
    match group_stack with
      | [] -> element_stack
      | (elem,att,elems)::g ->
          let e = {
            name = elem;
            attributes = att;
            elements = List.rev element_stack;
          }
          in pop_all g (e::elems)

  exception Parse_error of string

  let parse_error s = raise (Parse_error s)

}

let space = [' ' '\t' '\r' '\n']
let digit = ['0'-'9']
let letter = ['a'-'z' 'A'-'Z']
let ident = (letter | digit | '_') +
let sign = '-' | '+'
let integer = sign? digit+
let mantissa = ['e''E'] sign? digit+
let real = sign? digit* '.' digit* mantissa?
let escape = ['\\''"''n''t''r']

rule xml_prolog = parse
| space+
    { xml_prolog lexbuf }
| "<?xml" space+ "version=\"1.0\"" space+ "?>"
    { xml_doctype "1.0" "" lexbuf }
| "<?xml" space+ "version=\"1.0\"" space+ "encoding=\"UTF-8\"" space+ "?>"
    { xml_doctype "1.0" "" lexbuf }
| "<?xml" ([^'?']|'?'[^'>'])* "?>"
    { Format.eprintf "[Xml warning] prolog ignored@\n";
      xml_doctype "1.0" "" lexbuf }
| _
    { parse_error "wrong prolog" }

and xml_doctype version encoding = parse
| space+
    { xml_doctype version encoding lexbuf }
| "<!DOCTYPE" space+ (ident as doctype) space+ [^'>']* ">"
    { match elements [] [] lexbuf with
         | [x] ->
            { version = version;
              encoding = encoding;
              doctype = doctype;
              dtd = "";
              content = x;
            }
         | _ -> parse_error "there should be exactly one root element"
    }
| _
    { parse_error "wrong DOCTYPE" }

and elements group_stack element_stack = parse
  | space+
      { elements group_stack element_stack lexbuf }
  | '<' (ident as elem)
      { attributes group_stack element_stack elem [] lexbuf }
  | "</" (ident as celem) space* '>'
      { match group_stack with
         | [] ->
             Format.eprintf
               "[Xml warning] unexpected closing Xml element `%s'@\n"
               celem;
             elements group_stack element_stack lexbuf
         | (elem,att,stack)::g ->
             if celem <> elem then
               Format.eprintf
                 "[Xml warning] Xml element `%s' closed by `%s'@\n"
                 elem celem;
             let e = {
                name = elem;
                attributes = att;
                elements = List.rev element_stack;
             }
             in elements g (e::stack) lexbuf
       }
  | '<'
      { Format.eprintf "[Xml warning] unexpected '<'@\n";
        elements group_stack element_stack lexbuf }
  | eof
      { match group_stack with
         | [] -> element_stack
         | (elem,_,_)::_ ->
             Format.eprintf "[Xml warning] unclosed Xml element `%s'@\n" elem;
             pop_all group_stack element_stack
      }
  | _ as c
      { parse_error ("invalid element starting with " ^ String.make 1 c) }

and attributes groupe_stack element_stack elem acc = parse
  | space+
      { attributes groupe_stack element_stack elem acc lexbuf }
  | (ident as key) space* '='
      { let v = value lexbuf in
        attributes groupe_stack element_stack elem ((key,v)::acc) lexbuf }
  | '>'
      { elements ((elem,acc,element_stack)::groupe_stack) [] lexbuf }
  | "/>"
      { let e = { name = elem ;
                  attributes = acc;
                  elements = [] }
        in
        elements groupe_stack (e::element_stack) lexbuf }
  | _ as c
      { parse_error ("'>' expected, got " ^ String.make 1 c) }
  | eof
      { parse_error "unclosed element, `>' expected" }

and value = parse
  | space+
      { value lexbuf }
  | '"'
      { Buffer.clear buf;
        string_val lexbuf }
  | _ as c
      { parse_error ("invalid value starting with " ^ String.make 1 c) }
  | eof
      { parse_error "unterminated keyval pair" }

and string_val = parse
  | '"'
      { Buffer.contents buf }
  | [^ '\\' '"'] as c
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' (['\\''\"'] as c)
      { Buffer.add_char buf c;
        string_val lexbuf }
  | '\\' 'n'
      { Buffer.add_char buf '\n';
        string_val lexbuf }
  | '\\' (_ as c)
      { Buffer.add_char buf '\\';
        Buffer.add_char buf c;
        string_val lexbuf }
  | eof
      { parse_error "unterminated string" }

{

  let from_file f =
      let c = open_in f in
      let lb = Lexing.from_channel c in
      let t = xml_prolog lb in
      close_in c;
      t

}
