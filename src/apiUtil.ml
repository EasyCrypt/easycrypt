(** Useful things to build Api, but keep it separate because we don't want them
    * in the Api signature... *)

open EcUtil

type cmd = { name: string; args: string list;
             help: Format.formatter -> unit -> unit; }
let cmds = ref []

let add (c:cmd) = cmds := c::!cmds

let pp_cmd with_help c =
  let pp_args fmt l = match l with [] -> Format.fprintf fmt "()"
    | _ -> (pp_string_list ~sep:" ") fmt l
  in Format.printf "@[<5># %s %a;;@\n@[%a@]@]@."
  c.name pp_args c.args
  (if with_help then c.help else fun _ _ -> ()) ()

let pp_cmds with_help l = List.iter (pp_cmd with_help) l

let help_of_string str = fun fmt _ -> Format.pp_print_string fmt str
