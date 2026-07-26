type t = string

let equal = String.equal
let compare = String.compare
let hash = Hashtbl.hash
let to_string s = s
let of_string s = s
let pp fmt s = Format.pp_print_string fmt s
let of_hash_and_path ~hash ~path = hash ^ "@" ^ path

let of_source source =
  "s:" ^ Digest.to_hex (Digest.string source)

let stub_of_int n = Printf.sprintf "stub-%08d" n
