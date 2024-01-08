(* -------------------------------------------------------------------- *)
open Lospecs

(* -------------------------------------------------------------------- *)
let _ =
  let prog = Io.parse IO.stdin in
  let ast = Typing.tt_program Typing.Env.empty prog in
  let _dep = List.map Bitdep.bd_adef (List.map snd ast) in
  Format.eprintf "%a@."
    (Yojson.Safe.pretty_print ~std:true)
    (Ptree.pprogram_to_yojson prog)
