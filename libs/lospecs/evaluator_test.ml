open Lospecs.Evaluator
(* -------------------------------------------------------------------- *)

let a = BitWord.from_int64arr [| 2047L; 2047L |] 80
let b = BitWord.from_int64arr [| 23192381L; 123712832L |] 10
let () = Format.eprintf "%a@." 
        (Yojson.Safe.pretty_print ~std:true)
        (BitWord.bitword_to_yojson 
         (BitWord.sub a 60 10))
