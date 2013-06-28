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

val _dummy : t

val make      : position -> position -> t
val of_lexbuf : lexbuf -> t
val tostring  : t -> string
val merge     : t -> t -> t
val isdummy   : t -> bool

(* -------------------------------------------------------------------- *)
type 'a located = {
  pl_loc  : t;
  pl_desc : 'a;
}

val unloc  : 'a located -> 'a
val unlocs : ('a located) list -> 'a list
val mk_loc : t -> 'a -> 'a located
val lmap   : ('a -> 'b) -> 'a located -> 'b located

(* -------------------------------------------------------------------- *)
exception LocError of t * exn 

val locate_error : t -> exn -> 'a
