(* -------------------------------------------------------------------- *)
type ppdebug

(* -------------------------------------------------------------------- *)
type dnode = [`Node of string * dnode list]

val dnode : string -> dnode list -> dnode
val dleaf : ('a, unit, string, dnode) format4 -> 'a

(* -------------------------------------------------------------------- *)
val initial : ppdebug
val single  : ppdebug -> ?extra:string -> string -> unit

(* -------------------------------------------------------------------- *)
val onseq :    ppdebug
            -> ?enum:bool -> ?extra:string -> string
            -> (ppdebug -> unit) Stream.t
            -> unit
 
(* -------------------------------------------------------------------- *)
val onhseq :   ppdebug
            -> ?enum:bool -> ?extra:string -> string
            -> (ppdebug -> 'a -> unit)
            -> 'a Stream.t
            -> unit

(* -------------------------------------------------------------------- *)
val onhlist :   ppdebug
             -> ?enum:bool -> ?extra:string -> string
             -> (ppdebug -> 'a -> unit)
             -> 'a list
             -> unit

(* -------------------------------------------------------------------- *)
val ondnode : ppdebug -> dnode -> unit
