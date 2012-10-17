/**************************************************************************/
/*                                                                        */
/*  Copyright (C) 2010-2011                                               */
/*    François Bobot                                                      */
/*    Simon Cruanes                                                       */
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

  open TptpTree

  let translateSpecial t = let module M =
      Map.Make(struct type t=string let compare=String.compare end) in
    let known = List.fold_left (fun acc (x, y) -> M.add x y acc) M.empty [
      ("true", "true");
      ("false", "false")
    ] in
    try
      M.find t known
    with _ -> t

%}


(** set of tokens *)

%token<string> INT
%token LPAREN RPAREN LBRACKET RBRACKET
%token DOT COMMA COLON
%token PIPE AND ARROW LRARROW EQUAL NEQUAL NOT
%token BANG QUESTION DOLLAR
%token INCLUDE

%token<string> UIDENT
%token<string> LIDENT
%token<string> SINGLEQUOTED
%token FOF CNF
%token EOF

%right PIPE AND ARROW LRARROW
%nonassoc COLON
%nonassoc NOT

%start<TptpTree.decl list> tptp
%start<TptpTree.decl> decl

%%

tptp:
| e = decl* EOF
  { e }
(* | error
  { Printf.printf "error at lexing pos %i\n" $endpos.Lexing.pos_lnum; assert false } *)

decl:
| CNF LPAREN name = lident COMMA ty = decl_type COMMA f = fmla RPAREN DOT
  { Cnf (name, ty, f) }
| FOF LPAREN name = lident COMMA ty = decl_type COMMA f = fmla RPAREN DOT
  { Fof (name, ty, f) }
| INCLUDE LPAREN p = SINGLEQUOTED RPAREN DOT
  { Include p }

decl_type:
| x=lident
{ match x with
  | "axiom" -> Axiom
  | "hypothesis" -> Axiom
  | "assumption" -> Axiom
  | "definition" -> Axiom
  | "conjecture" -> Conjecture
  | "negated_conjecture" -> NegatedConjecture
  | "lemma" -> Lemma
  | "theorem" -> Lemma
  | _ -> raise Error }


fmla:
| quant = quantifier LBRACKET vars = separated_nonempty_list(COMMA, variable)
    RBRACKET
  COLON f = fmla
  { FQuant (quant, vars, f) }
| LPAREN f = fmla RPAREN
  { f }
| f1 = fmla op = logic_binop f2 = fmla
  { FBinop (op, f1, f2) }
| op = logic_unop f = fmla
  { FUnop (op, f) }
| funct = lident LPAREN terms = separated_list(COMMA, term) RPAREN
  { FPred (funct, terms) }
| t1 = term op = term_binop t2 = term
  { FTermBinop (op, t1, t2) }


term:
| DOLLAR atom = lident
  { TAtom (translateSpecial atom) }
| atom = lident
  { TAtom atom }
| c = INT
  { TConst c }
| var = uident
  { TVar var }
| funct = lident LPAREN terms = separated_list(COMMA, term) RPAREN
  { TFunctor (funct, terms) }


lident:
| i = SINGLEQUOTED { i }
| i = LIDENT { i }
uident:
| i = UIDENT { i }
%inline variable:
| i = uident { i }
%inline quantifier:
| BANG { Forall }
| QUESTION { Exist }
%inline logic_binop:
| PIPE { Or }
| AND { And }
| ARROW { Implies }
| LRARROW { Equiv }
%inline logic_unop:
| NOT { Not }
%inline term_binop:
| EQUAL { Equal }
| NEQUAL { NotEqual }
