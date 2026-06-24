(* -------------------------------------------------------------------- *)
open Ptree

(* -------------------------------------------------------------------- *)
(* [parse name input] parses a lospecs program from [input], tagging
   source locations with the file name [name]. *)
val parse : string -> IO.input -> pprogram
