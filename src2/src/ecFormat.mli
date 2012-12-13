(* -------------------------------------------------------------------- *)
open Format

type 'a pp = formatter -> 'a -> unit

(* -------------------------------------------------------------------- *)
val pp_err : 'a pp -> 'a -> unit

val pp_void  : 'a pp
val pp_unit  : unit pp
val pp_int   : int pp
val pp_string: string pp

val pp_id   : 'a pp -> 'a pp
val pp_pair : 'a pp -> 'b pp -> ('a * 'b) pp
val pp_paren: 'a pp -> 'a pp

val pp_option:
     ?pre:('a, 'b, 'c, 'd, 'd, 'a) format6
  -> ?pst:('i, 'j, 'k, 'l, 'l, 'i) format6
  -> 'm pp -> ('m option) pp

val pp_list :
     ?pre:('a, 'b, 'c, 'd, 'd, 'a) format6
  -> ?sep:('e, 'f, 'g, 'h, 'h, 'e) format6
  -> ?pst:('i, 'j, 'k, 'l, 'l, 'i) format6
  -> 'm pp -> ('m list) pp
