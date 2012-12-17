(* -------------------------------------------------------------------- *)
type ppdebug

(* -------------------------------------------------------------------- *)
val initial : ppdebug
val single  : ppdebug -> ?extra:string -> string -> unit

(* -------------------------------------------------------------------- *)
val onseq :    ppdebug
            -> ?extra:string -> string
            -> (ppdebug -> unit) Stream.t
            -> unit
 
(* -------------------------------------------------------------------- *)
val onhseq :   ppdebug
            -> ?extra:string -> string
            -> (ppdebug -> 'a -> unit)
            -> 'a Stream.t
            -> unit

(* -------------------------------------------------------------------- *)
val onhlist :   ppdebug
             -> ?extra:string -> string
             -> (ppdebug -> 'a -> unit)
             -> 'a list
             -> unit
