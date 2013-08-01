(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type ecloader = {
  mutable ecl_idirs : (bool * string) list;
}

(* -------------------------------------------------------------------- *)
let create () = { ecl_idirs = []; }

(* -------------------------------------------------------------------- *)
let aslist (ld : ecloader) =
  ld.ecl_idirs

(* -------------------------------------------------------------------- *)
let dup (ld : ecloader) = { ecl_idirs = ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let forsys (ld : ecloader) =
  { ecl_idirs = List.filter (fun (b, _) -> b) ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let addidir ?(system = false) (idir : string) (ecl : ecloader) =
  ecl.ecl_idirs <- (system, idir) :: ecl.ecl_idirs

(* -------------------------------------------------------------------- *)
let check_case idir name (dev, ino) =
  let check1 oname =
      match name = oname with
      | false -> false
      | true  -> begin
          try
            let stat = Filename.concat idir oname in
            let stat = Unix.lstat stat in
              stat.Unix.st_dev = dev && stat.Unix.st_ino = ino
          with Unix.Unix_error _ -> false
      end
  in
    try  List.exists check1 (EcUtils.Os.listdir idir)
    with Unix.Unix_error _ -> false

(* -------------------------------------------------------------------- *)
let locate ?(onlysys = false) (name : string) (ecl : ecloader) =
  if not (Str.string_match (Str.regexp "^[a-zA-Z0-9]+$") name 0) then
    None
  else
    let iname = Printf.sprintf "%s.ec" name in
    let oname = String.copy iname in
  
    iname.[0] <- Char.lowercase iname.[0];
    oname.[0] <- Char.uppercase oname.[0];
  
    let locate (issys, idir) =
      List.pick
        (fun name ->
          match onlysys && not issys with
          | true  -> None
          | false -> begin
              let name = Filename.concat idir name in
              let stat = try  Some (Unix.lstat name)
                         with Unix.Unix_error _ -> None
              in
                match stat with
                | None -> None
                | Some stat ->
                  let stat = (stat.Unix.st_dev, stat.Unix.st_ino) in
                    if   not (check_case idir oname stat)
                    then None
                    else Some name
          end)
        [iname; oname]
    in
      List.pick locate ecl.ecl_idirs
