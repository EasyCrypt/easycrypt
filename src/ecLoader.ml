(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ecloader = {
  mutable ecl_idirs : (bool * string) list;
}

(* -------------------------------------------------------------------- *)
let create () = { ecl_idirs = []; }

(* -------------------------------------------------------------------- *)
let dup (ld : ecloader) = { ecl_idirs = ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let forsys (ld : ecloader) =
  { ecl_idirs = List.filter (fun (b, _) -> b) ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let addidir ?(system = false) (idir : string) (ecl : ecloader) =
  ecl.ecl_idirs <- (system, idir) :: ecl.ecl_idirs

(* -------------------------------------------------------------------- *)
let locate ?(onlysys = false) (name : string) (ecl : ecloader) =
  let iname = Printf.sprintf "%s.ec" name in
  let oname = String.copy iname in

    iname.[0] <- Char.lowercase iname.[0];
    oname.[0] <- Char.uppercase oname.[0];

  let locate (issys, idir) =
    List.pick
      (fun name ->
        if   onlysys && not issys
        then None
        else
          let name = Filename.concat idir name in
            if   Sys.file_exists name
            then Some name
            else None)
      [iname; oname]
  in
    List.pick locate ecl.ecl_idirs
