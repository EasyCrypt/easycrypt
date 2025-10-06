/* A small library to read and write .ini files

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
*/


%token Newline EOF
%token <string> Section
%token <string * string> Value
%type <(string * ((string * string) list)) list> inifile
%start inifile
%%

values:
  Value Newline values {$1 :: $3}
| Value Newline {[$1]}

ini:
  Section Newline values inifile {($1, $3) :: $4}
| Section Newline values {[($1, $3)]}

inifile:
  ini EOF {$1}
| Newline ini EOF {$2}
