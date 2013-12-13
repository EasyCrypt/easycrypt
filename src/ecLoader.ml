(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type idx_t = int * int

type ecloader = {
  mutable ecl_idirs : ((bool * string) * idx_t) list;
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
  { ecl_idirs = List.filter (fun ((b, _), _) -> b) ld.ecl_idirs; }

(* -------------------------------------------------------------------- *)
let rec addidir ?(system = false) ?(recursive = false) (idir : string) (ecl : ecloader) =
  if recursive then begin
    let isdir filename =
      let filename = Filename.concat idir filename in
        try Sys.is_directory filename with Sys_error _ -> false
    in

    let dirs = (try EcUtils.Os.listdir idir with Unix.Unix_error _ -> []) in
    let dirs = List.sort compare (List.filter isdir dirs) in

      List.iter (fun filename ->
        if not (String.startswith "." filename) then
          let filename = Filename.concat idir filename in
            addidir ~system ~recursive filename ecl)
        dirs
  end;

  match (try Some (Unix.stat idir) with Unix.Unix_error _ -> None) with
  | None    -> ()
  | Some st ->
      let idx = (st.Unix.st_dev, st.Unix.st_ino) in
        if not (List.exists ((=) idx |- snd) ecl.ecl_idirs) then
            ecl.ecl_idirs <- ((system, idir), idx) :: ecl.ecl_idirs

(* -------------------------------------------------------------------- *)
let try_stat name =
  try  Some (Unix.lstat name)
  with Unix.Unix_error _ -> None

(* -------------------------------------------------------------------- *)
let norm_name name =
  let name = String.copy name in
    if String.length name > 0 then
      name.[0] <- Char.lowercase name.[0];
    name

(* -------------------------------------------------------------------- *)
let check_case idir name (dev, ino) =
  let name = norm_name name in

  let check1 tname =
      match name = norm_name tname with
      | false -> false
      | true  -> begin
          try
            let stat = Filename.concat idir tname in
            let stat = Unix.lstat stat in
              stat.Unix.st_dev = dev && stat.Unix.st_ino = ino
          with Unix.Unix_error _ -> false
      end
  in
    try  List.exists check1 (EcUtils.Os.listdir idir)
    with Unix.Unix_error _ -> false

(* -------------------------------------------------------------------- *)
let locate ?(onlysys = false) (name : string) (ecl : ecloader) =
  if not (Str.string_match (Str.regexp "^[a-zA-Z0-9_]+$") name 0) then
    None
  else
    let name = Printf.sprintf "%s.ec" name in
  
    let locate ((issys, idir), _) =
      match onlysys && not issys with
      | true  -> None
      | false ->
        let stat =
          let oname = String.copy name in
          let iname = String.copy name in
            oname.[0] <- Char.uppercase oname.[0];
            iname.[0] <- Char.lowercase iname.[0];
            List.fpick
              (List.map
                 (fun name ->
                   let fullname = Filename.concat idir name in
                     fun () -> try_stat fullname |> omap (fun s -> (s, name)))
                 [iname; oname])
        in
          match stat with
          | None -> None
          | Some (stat, name) ->
            let stat = (stat.Unix.st_dev, stat.Unix.st_ino) in
              if   not (check_case idir name stat)
              then None
              else Some (Filename.concat idir name)
    in
      List.pick locate ecl.ecl_idirs
