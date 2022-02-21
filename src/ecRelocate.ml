let myname = Filename.basename Sys.executable_name
let mydir  = Filename.dirname  Sys.executable_name

let eclocal =
  let rex = EcRegexp.regexp "^ec\\.(?:native|byte|exe)$" in
  EcRegexp.match_ (`C rex) myname

let sourceroot =
  if eclocal then
    if   Filename.basename mydir = "src"
    then Some mydir
    else Some (Filename.concat mydir "src")
  else None

let resource name =
  match eclocal with
  | true ->
      if Filename.basename mydir = "src" then
        List.fold_left Filename.concat mydir
          ([Filename.parent_dir_name] @ name)
      else
        List.fold_left Filename.concat mydir name

  | false ->
      List.fold_left Filename.concat mydir
        ([Filename.parent_dir_name; "lib"; "easycrypt"] @ name)

module Sites = struct
  let theories = [resource ["theories"]]
end
