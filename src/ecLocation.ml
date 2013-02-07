open Lexing

type t = {
    loc_fname : string;
    loc_start : int * int;
    loc_end   : int * int;
  }

let dummy = {
  loc_fname = "";
  loc_start = (-1, -1);
  loc_end   = (-1, -1);
}

let make (p1 : position) (p2 : position) =
  let mkpos (p : position) =
    (p.pos_lnum, p.pos_cnum - p.pos_bol)
  in
  { loc_fname = p1.pos_fname;
    loc_start = mkpos p1    ;
    loc_end   = mkpos p2    ; }

let of_lexbuf (lb : lexbuf) =
  let p1 = Lexing.lexeme_start_p lb in
  let p2 = Lexing.lexeme_end_p lb in
  make p1 p2

let tostring (p : t) =
  Printf.sprintf "%s:%d.%d-%d.%d"
    p.loc_fname
    (fst p.loc_start) (snd p.loc_start)
    (fst p.loc_end  ) (snd p.loc_end  )
      
exception LocError of t * exn 

let locate_error loc exn = 
  match exn with
  | LocError _ -> raise exn
  | _ -> raise (LocError(loc,exn))

let pp_located loc pp_elt fmt x =
  Format.fprintf fmt "%s: %a" (tostring loc) pp_elt x

let pp_error fmt exn = 
  match exn with
  | LocError (loc,exn) ->
      pp_located loc EcPexception.exn_printer fmt exn
  | _ -> raise exn 

let _ = EcPexception.register pp_error

