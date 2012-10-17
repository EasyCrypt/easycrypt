/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-2011                                               */
/*    François Bobot                                                      */
/*    Jean-Christophe Filliâtre                                           */
/*    Claude Marché                                                       */
/*    Andrei Paskevich                                                    */
/*                                                                        */
/*  This software is free software; you can redistribute it and/or        */
/*  modify it under the terms of the GNU Library General Public           */
/*  License version 2.1, with the special exception on linking            */
/*  described in file LICENSE.                                            */
/*                                                                        */
/*  This software is distributed in the hope that it will be useful,      */
/*  but WITHOUT ANY WARRANTY; without even the implied warranty of        */
/*  MERCHANTABILITY or FITNESS FOR A PARTICULAR PURPOSE.                  */
/*                                                                        */
/**************************************************************************/

%{
  open Driver_ast
  open Parsing
  let loc () = Loc.extract (symbol_start_pos (), symbol_end_pos ())
  let loc_i i = Loc.extract (rhs_start_pos i, rhs_end_pos i)
  let infix s = "infix " ^ s
  let prefix s = "prefix " ^ s
  let mixfix s = "mixfix " ^ s
%}

%token <string> INPUT /* never reaches the parser */

%token <int> INTEGER
%token <string> IDENT
%token <string> STRING
%token <string> OPERATOR
%token THEORY END SYNTAX REMOVE META PRELUDE PRINTER
%token VALID INVALID TIMEOUT UNKNOWN FAIL TIME
%token UNDERSCORE LEFTPAR RIGHTPAR CLONED DOT EOF
%token FUNCTION PREDICATE TYPE PROP FILENAME TRANSFORM PLUGIN
%token LEFTPAR_STAR_RIGHTPAR COMMA
%token LEFTSQ RIGHTSQ LARROW

%type <Driver_ast.file> file
%start file

%%

file:
| list0_global_theory EOF
    { $1 }
;

list0_global_theory:
| /* epsilon */      { { f_global = []; f_rules = [] } }
| global list0_global_theory
    { {$2 with f_global = (loc_i 1, $1) :: ($2.f_global)} }
| theory list0_global_theory
    { {$2 with f_rules = $1 :: ($2.f_rules)} }
;

global:
| PRELUDE STRING { Prelude $2 }
| PRINTER STRING { Printer $2 }
| VALID STRING { RegexpValid $2 }
| INVALID STRING { RegexpInvalid $2 }
| TIMEOUT STRING { RegexpTimeout $2 }
| TIME STRING  { TimeRegexp $2 }
| UNKNOWN STRING STRING { RegexpUnknown ($2, $3) }
| FAIL STRING STRING { RegexpFailure ($2, $3) }
| VALID INTEGER { ExitCodeValid $2 }
| INVALID INTEGER { ExitCodeInvalid $2 }
| TIMEOUT INTEGER { ExitCodeTimeout $2 }
| UNKNOWN INTEGER STRING { ExitCodeUnknown ($2, $3) }
| FAIL INTEGER STRING { ExitCodeFailure ($2, $3) }
| FILENAME STRING { Filename $2 }
| TRANSFORM STRING { Transform $2 }
| PLUGIN STRING STRING { Plugin ($2,$3) }
;

theory:
| THEORY tqualid list0_trule END
    { { thr_name = $2; thr_rules = $3 } }
;

list0_trule:
| /* epsilon */     { [] }
| trule list0_trule { (loc_i 1, $1) :: $2 }
;

trule:
| PRELUDE STRING                          { Rprelude  ($2) }
| SYNTAX cloned TYPE      qualid STRING   { Rsyntaxts ($2, $4, $5) }
| SYNTAX cloned FUNCTION  qualid STRING   { Rsyntaxfs ($2, $4, $5) }
| SYNTAX cloned PREDICATE qualid STRING   { Rsyntaxps ($2, $4, $5) }
| REMOVE cloned PROP qualid               { Rremovepr ($2, $4) }
| META cloned ident meta_args             { Rmeta     ($2, $3, $4) }
| META cloned STRING meta_args            { Rmeta     ($2, $3, $4) }
;

meta_args:
| meta_arg                 { [$1] }
| meta_arg COMMA meta_args { $1 :: $3 }
;

meta_arg:
| TYPE      qualid { PMAts  $2 }
| FUNCTION  qualid { PMAfs  $2 }
| PREDICATE qualid { PMAps  $2 }
| PROP      qualid { PMApr  $2 }
| STRING           { PMAstr $1 }
| INTEGER          { PMAint $1 }
;

cloned:
| /* epsilon */ { false }
| CLONED        { true  }
;

tqualid:
| ident             { loc (), [$1] }
| ident DOT tqualid { loc (), ($1 :: snd $3) }
;

qualid:
| ident_rich        { loc (), [$1] }
| ident DOT qualid  { loc (), ($1 :: snd $3) }
;

ident:
| IDENT     { $1 }
| SYNTAX    { "syntax" }
| REMOVE    { "remove" }
/*
| CLONED    { "cloned" }
*/
| PRELUDE   { "prelude" }
| PRINTER   { "printer" }
| VALID     { "valid" }
| INVALID   { "invalid" }
| TIMEOUT   { "timeout" }
| UNKNOWN   { "unknown" }
| FAIL      { "fail" }
| FILENAME  { "filename" }
| TRANSFORM { "transformation" }
| PLUGIN    { "plugin" }
;

ident_rich:
| ident                     { $1 }
| LEFTPAR_STAR_RIGHTPAR     { infix "*" }
| LEFTPAR operator RIGHTPAR { $2 }
;

operator:
| OPERATOR              { infix $1 }
| OPERATOR UNDERSCORE   { prefix $1 }
| LEFTSQ RIGHTSQ        { mixfix "[]" }
| LEFTSQ LARROW RIGHTSQ { mixfix "[<-]" }
;

