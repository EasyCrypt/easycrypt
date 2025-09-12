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


{
  open Parseini
}

let newline = '\n' +
let whsp = ( [ ' ' '\t' ] | '\\' newline ) *
let id = ['-' '_' ':' '0' - '9' 'A' - 'Z' 'a' - 'z' ] +
let value = ( [ '\t' ' ' - '~' ] | '\\' newline | '\\' '#' ) +

rule lexini = parse
    whsp '[' whsp (id as id) whsp ']' {Section id}
  | whsp (id as id) whsp '=' whsp (value as value) whsp {Value (id, value)}
  | newline {Newline}
  | eof {EOF}
