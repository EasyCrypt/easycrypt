let myname = Filename.basename Sys.executable_name
let mydir  = Filename.dirname  Sys.executable_name

let eclocal =
  let rex = EcRegexp.regexp "^ec\\.(?:native|byte|exe)$" in
  EcRegexp.match_ (`C rex) myname

let sourceroot =
  if eclocal then
    if   Filename.basename mydir = "src"
    then Some (Filename.dirname mydir)
    else Some mydir
  else None

let resource (name : string list) =
  match eclocal with
  | true ->
      let root =
        if Filename.basename mydir = "src" then
          Filename.concat mydir Filename.parent_dir_name
        else mydir in

      List.fold_left
        Filename.concat root
        (["_build"; "install"; "default"; "lib"; "easycrypt"] @ name)

  | false ->
      List.fold_left Filename.concat mydir
        ([Filename.parent_dir_name; "lib"; "easycrypt"] @ name)

module Sites = struct
  let theories = [resource ["theories"]]

  let doc = resource ["doc"]
end
