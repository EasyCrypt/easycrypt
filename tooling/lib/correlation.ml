type t = string

let of_client s = "c:" ^ s

let counter = ref 0

let fresh () =
  incr counter;
  Printf.sprintf "d:%06d" !counter

let to_string s = s
let equal = String.equal
let pp fmt s = Format.pp_print_string fmt s
