(* -------------------------------------------------------------------- *)
open Lexing

(* -------------------------------------------------------------------- *)
type t = {
  loc_fname : string;
  loc_start : int * int;
  loc_end   : int * int;
  loc_bchar : int;
  loc_echar : int;
}

let _dummy = {
  loc_fname = "";
  loc_start = (-1, -1);
  loc_end   = (-1, -1);
  loc_bchar = -1;
  loc_echar = -1;
}

let make (p1 : position) (p2 : position) =
  let mkpos (p : position) =
    (p.pos_lnum, p.pos_cnum - p.pos_bol)
  in
    { loc_fname = p1.pos_fname;
      loc_start = mkpos p1    ;
      loc_end   = mkpos p2    ;
      loc_bchar = p1.pos_cnum ;
      loc_echar = p2.pos_cnum ; }

let of_lexbuf (lb : lexbuf) =
  let p1 = Lexing.lexeme_start_p lb in
  let p2 = Lexing.lexeme_end_p lb in
  make p1 p2

let tostring (p : t) =
  let spos =
    if p.loc_start = p.loc_end then
      Printf.sprintf "line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
    else if fst p.loc_start = fst p.loc_end then
      Printf.sprintf "line %d (%d-%d)"
        (fst p.loc_start) (snd p.loc_start) (snd p.loc_end)
    else
      Printf.sprintf "line %d (%d) to line %d (%d)"
        (fst p.loc_start) (snd p.loc_start)
        (fst p.loc_end  ) (snd p.loc_end  )
  in
    Printf.sprintf "%s: %s" p.loc_fname spos

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

let unloc  x = x.pl_desc
let unlocs x = List.map unloc x

let lmap f x = 
  { x with pl_desc = f x.pl_desc }

let mk_loc loc x = { pl_loc = loc; pl_desc = x; }

(* -------------------------------------------------------------------- *)      
exception LocError of t * exn 

let locate_error loc exn = 
  match exn with
  | LocError _ -> raise exn
  | _ -> raise (LocError(loc,exn))
