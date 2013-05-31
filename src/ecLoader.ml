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
  ecl.ecl_idirs <- idir :: ecl.ecl_idirs

(* -------------------------------------------------------------------- *)
let locate (name : string) (ecl : ecloader) =
  let iname = Printf.sprintf "%s.ec" name in
  let oname = String.copy iname in

    iname.[0] <- Char.lowercase iname.[0];
    oname.[0] <- Char.uppercase oname.[0];

  let locate idir =
    List.pick
      (fun name ->
         let name = Filename.concat idir name in
           if Sys.file_exists name then
             Some name
           else
             None)
      [iname; oname]
  in
    List.pick locate ecl.ecl_idirs
