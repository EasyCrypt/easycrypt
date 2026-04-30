(* -------------------------------------------------------------------- *)
let myname = Filename.basename Sys.executable_name
let mydir  = Filename.dirname  Sys.executable_name

(* -------------------------------------------------------------------- *)
let eclocal : bool =
  let rex = EcRegexp.regexp "^ec\\.(?:native|byte|exe)$" in
  EcRegexp.match_ (`C rex) myname

(* -------------------------------------------------------------------- *)
let sourceroot : string option =
  if eclocal then
    if   Filename.basename mydir = "src"
    then Some (Filename.dirname mydir)
    else Some mydir
  else None

(* -------------------------------------------------------------------- *)
let local (name : string list) : string =
  List.fold_left Filename.concat (Option.value ~default:"." sourceroot) name

(* -------------------------------------------------------------------- *)
module type Sites = sig
  val commands : string
  val theories : string list
  val doc      : string
  val config   : string
end

(* -------------------------------------------------------------------- *)
module LocalSites() : Sites = struct
  let commands = local ["scripts"; "testing"]
  let theories = [local ["theories"]]
  let doc = local ["assets"; "styles"]
  let config   = local ["etc"]
end

(* -------------------------------------------------------------------- *)
module DuneSites() : Sites = struct
  let commands =
    Option.value ~default:"."
      (EcUtils.List.Exceptionless.hd EcDuneSites.Sites.commands)

  let theories =
    EcDuneSites.Sites.theories

  let doc =
    Option.value ~default:"."
      (EcUtils.List.Exceptionless.hd EcDuneSites.Sites.doc)

      let config =
    Option.value ~default:"etc"
      (EcUtils.List.Exceptionless.hd EcDuneSites.Sites.config)
end

(* -------------------------------------------------------------------- *)
let sites : (module Sites) =
  if   eclocal
  then (module LocalSites ())
  else (module DuneSites ())
