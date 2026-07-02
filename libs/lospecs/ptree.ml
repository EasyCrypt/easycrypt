(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type range = {
  rg_fname : string;
  rg_begin : int * int;
  rg_end   : int * int;  
}

type 'a loced = { range : range; data : 'a; }

(* -------------------------------------------------------------------- *)
module Lc = struct
  let of_positions (p1 : position) (p2 : position) : range =
    assert (p1.pos_fname = p2.pos_fname);

    let mk_range (p : position) =
      (p.pos_lnum, p.pos_cnum - p.pos_bol) in

    { rg_fname = p1.pos_fname; rg_begin = mk_range p1; rg_end = mk_range p2; }

  let of_lexbuf (lx : Lexing.lexbuf) : range =
    let p1 = Lexing.lexeme_start_p lx in
    let p2 = Lexing.lexeme_end_p lx in
    of_positions p1 p2

  let merge (p1 : range) (p2 : range) =
    assert (p1.rg_fname = p2.rg_fname);
    { rg_fname = p1.rg_fname;
      rg_begin = min p1.rg_begin p2.rg_begin;
      rg_end   = max p1.rg_end   p2.rg_end; }

  let unloc (x : 'a loced) : 'a =
    x.data

  let mk (range : range) (data : 'a) : 'a loced =
    { range; data; }

  let map (f : 'a -> 'b) (x : 'a loced) : 'b loced =
    { x with data = f x.data }
end

(* -------------------------------------------------------------------- *)
exception ParseError of range

(* -------------------------------------------------------------------- *)
type symbol = string
type word = [ `W of int ]
type type_ = [ `Unsigned | `Signed | word ]

(* -------------------------------------------------------------------- *)
type psymbol = symbol loced
type pword = word loced
type ptype = type_ loced
type parg = psymbol * pword
type pargs = parg list
type pfname = (psymbol * pword list option) loced

(* -------------------------------------------------------------------- *)
type pexpr_ =
  | PEParens of pexpr 
  | PEFName of pfname
  | PEInt of int64 * pword option
  | PECond of pexpr * (pexpr * pexpr)
  | PEFun of pargs * pexpr
  | PELet of (psymbol * pargs option * pexpr) * pexpr
  | PESlice of pexpr * pslice
  | PEAssign of pexpr * pslice * pexpr
  | PEApp of pfname * pexpr option loced list

and pexpr = pexpr_ loced

and pslice = (pexpr * pexpr option * pexpr option)

type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }

type pprogram = pdef list
