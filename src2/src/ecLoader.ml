(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ecloader = {
  mutable ecl_idirs : string list;
}

(* -------------------------------------------------------------------- *)
let create () = {
  ecl_idirs = [];
}

(* -------------------------------------------------------------------- *)
let addidir (idir : string) (ecl : ecloader) =
  ecl.ecl_idirs <- ecl.ecl_idirs @ [idir]

(* -------------------------------------------------------------------- *)
let locate (name : string) (ecl : ecloader) =
  let fullname = Printf.sprintf "%s.ec" name in
  let locate idir =
    let fullname = Filename.concat idir fullname in
      if   Sys.file_exists fullname
      then Some fullname
      else None
  in
    List.pick locate ecl.ecl_idirs
