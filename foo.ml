module F = Format

let ifmt fmt =
  let norm =
    let re1 = Str.regexp "\r?\n"  in
    let re2 = Str.regexp " +" in
      fun x -> Str.global_replace re2 " " (Str.global_replace re1 " " x)
  in

  let output x i o = F.pp_print_string fmt (norm (String.sub x i o))
  and flush  ()    = F.pp_print_flush  fmt ()
  in
    F.make_formatter output flush

let pp1 fmt =
  F.fprintf fmt "@[<hov 10>%s@ %s@]"
    "-----------------------------------------------------------------"
    "'''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''''"

let _ = F.fprintf (ifmt F.err_formatter) "@[<h>%t@]@." pp1
