(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type range = {
  rg_fname : string;
  rg_begin : int * int;
  rg_end   : int * int;  
} [@@deriving yojson]

type 'a loced = { range : range; data : 'a; } [@@deriving yojson]

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
  
  let mergeall (p : range list) =
    match p with
    | [] -> assert false
    | t :: ts -> List.fold_left merge t ts

  let unloc (x : 'a loced) : 'a =
    x.data

  let range (x : 'a loced) : range =
    x.range

  let mk (range : range) (data : 'a) : 'a loced =
    { range; data; }

  let map (f : 'a -> 'b) (x : 'a loced) : 'b loced =
    { x with data = f x.data }

  let string_of_range (range : range) =
    let spos =
      if range.rg_begin = range.rg_end then
        Printf.sprintf "line %d (%d)"
          (fst range.rg_begin) (snd range.rg_begin + 1)
      else if fst range.rg_begin = fst range.rg_end then
        Printf.sprintf "line %d (%d-%d)"
          (fst range.rg_begin) (snd range.rg_begin + 1) (snd range.rg_end + 1)
      else
        Printf.sprintf "line %d (%d) to line %d (%d)"
          (fst range.rg_begin) (snd range.rg_begin + 1)
          (fst range.rg_end  ) (snd range.rg_end   + 1)
    in
      Printf.sprintf "%s: %s" range.rg_fname spos

  let pp_range (fmt : Format.formatter) (range : range) =
    Format.fprintf fmt "%s" (string_of_range range)
end

(* -------------------------------------------------------------------- *)
exception ParseError of range

(* -------------------------------------------------------------------- *)
type symbol = string [@@deriving yojson]
type word = [ `W of int ] [@@deriving yojson]
type type_ = [ `Unsigned | `Signed | word ] [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type psymbol = symbol loced [@@deriving yojson]
type pword = word loced [@@deriving yojson]
type ptype = type_ loced [@@deriving yojson]
type parg = psymbol * pword [@@deriving yojson]
type pargs = parg list [@@deriving yojson]
type pfname = (psymbol * pword list option) loced [@@deriving yojson]

(* -------------------------------------------------------------------- *)
type pexpr_ =
  | PEParens of pexpr 
  | PEFName of pfname
  | PEInt of int * pword option
  | PECond of pexpr * (pexpr * pexpr)
  | PEFun of pargs * pexpr
  | PELet of (psymbol * pargs option * pexpr) * pexpr
  | PESlice of pexpr * pslice
  | PEAssign of pexpr * pslice * pexpr
  | PEApp of pfname * pexpr option loced list
[@@deriving yojson]

and pexpr = pexpr_ loced [@@deriving yojson]

and pslice = (pexpr * pexpr option * pexpr option) [@@deriving yojson]

type pdef = { name : symbol; args : pargs; rty : pword; body : pexpr }
[@@deriving yojson]

type pprogram = pdef list [@@deriving yojson]
