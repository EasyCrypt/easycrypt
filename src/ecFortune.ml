(* --------------------------------------------------------------------- *)
open EcUtils

(* --------------------------------------------------------------------- *)
let pick : unit -> string option =
  let values = List.pmap b64decode EcCoreFortune.value in
  let values = Array.of_list values in

    fun () ->
      match Array.length values with
      | n when n <= 0 -> None
      | n -> Some (values.(Random.int n))
