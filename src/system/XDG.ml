(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
type path = string

type xdgroots = {
  xdg_data_home   : path;
  xdg_config_home : path;
  xdg_cache_home  : path;
  xdg_data_dirs   : path list;
  xdg_config_dirs : path list;
}

exception XdgUndefined of string

(* -------------------------------------------------------------------- *)
module Filename = struct
  include Filename

  let combine = function
    | [] -> invalid_arg "Filename.concat []"
    | x :: xs -> List.fold_left Filename.concat x xs

  let path_sep =
    match Sys.os_type with "Win32" -> ';' | _ -> ':'

  let paths_of_string s =
    let rex = String.make 1 path_sep in
    let rex = EcRegexp.regexp ((EcRegexp.quote rex) ^ "+") in
    EcRegexp.split0 (`C rex) s
end

(* -------------------------------------------------------------------- *)
module Internal = struct
  type system = [`Win32 | `Unix]

  let system : system =
    match Sys.os_type with
    | "Win32" -> `Win32
    | _       -> `Unix

  type 'a default = system -> 'a

  let getenv ?default name =
    try
      try  Sys.getenv name
      with Not_found ->
        match default with
        | None   -> raise Not_found
        | Some f -> f system

    with Not_found ->
      raise (XdgUndefined name)

  let getpath ?default name =
    Filename.paths_of_string (getenv ?default name)

  let get_system_home (_ : system) =
    (Unix.getpwuid (Unix.getuid ())).Unix.pw_dir

  let getfiles ?roots ?(exists=true) ~appname ~mode (user, osystem) name =
    let user   () = user ?roots () in
    let system () = match osystem with None -> [] | Some f -> f ?roots () in

    let alldirs =
      match mode with
      | `All    -> user () :: system ()
      | `User   -> [user ()]
      | `System -> system ()
    in

    List.fold_right (fun dir acc ->
        let fullpath = Filename.combine [dir; appname; name] in
        if   not exists || Sys.file_exists fullpath
        then fullpath :: acc
        else acc)
      alldirs []
end

(* -------------------------------------------------------------------- *)
type mode = [`User | `System | `All]

type xdgfile =
     ?roots:xdgroots
  -> ?exists:bool
  -> appname:string
  -> mode:mode
  -> path
  -> path list

(* -------------------------------------------------------------------- *)
let home = Internal.getenv ~default:Internal.get_system_home "HOME"

(* -------------------------------------------------------------------- *)
module Defaults = struct
  let xdg_data_home = function
    | `Win32 -> Unix.getenv "AppData"
    | `Unix  -> Filename.combine [home; ".local"; "share"]

  let xdg_config_home = function
    | `Win32 -> Filename.combine [home; "Local Settings"]
    | `Unix  -> Filename.combine [home; ".config"]

  let xdg_cache_home = function
    | `Win32 -> Filename.combine [home; "Local Settings"; "Cache"]
    | `Unix  -> Filename.combine [home; ".cache"]

  let xdg_data_dirs = function
    | `Win32 -> Unix.getenv "ProgramFiles"
    | `Unix  -> "/usr/local/share:/usr/share"


  let xdg_config_dirs = function
    | `Win32 -> Unix.getenv "ProgramFiles"
    | `Unix  -> "/etc/xdg"
end

(* -------------------------------------------------------------------- *)
let xdgroots =
  let module I = Internal in

  { xdg_data_home   = I.getenv  ~default:Defaults.xdg_data_home   "XDG_DATA_HOME"  ;
    xdg_config_home = I.getenv  ~default:Defaults.xdg_config_home "XDG_CONFIG_HOME";
    xdg_cache_home  = I.getenv  ~default:Defaults.xdg_cache_home  "XDG_CACHE_HOME" ;
    xdg_data_dirs   = I.getpath ~default:Defaults.xdg_data_dirs   "XDG_DATA_DIRS"  ;
    xdg_config_dirs = I.getpath ~default:Defaults.xdg_config_dirs "XDG_CONFIG_DIRS"; }

(* -------------------------------------------------------------------- *)
module Data = struct
  let user ?(roots = xdgroots) () =
    roots.xdg_data_home

  let system ?(roots = xdgroots) () =
    roots.xdg_data_dirs

  let all ?roots () =
    (user ?roots ()) :: (system ?roots ())

  let file ?roots ?exists ~appname ~mode =
    Internal.getfiles ?roots ?exists ~appname ~mode (user, Some system)
end

(* -------------------------------------------------------------------- *)
module Config = struct
  let user ?(roots = xdgroots) () =
    roots.xdg_config_home

  let system ?(roots = xdgroots) () =
    roots.xdg_config_dirs

  let all ?roots () =
    (user ?roots ()) :: (system ?roots ())

  let file ?roots ?exists ~appname ~mode =
    Internal.getfiles ?roots ?exists ~appname ~mode (user, Some system)
end

(* -------------------------------------------------------------------- *)
module Cache = struct
  let user ?(roots = xdgroots) () =
    roots.xdg_cache_home

  let file ?roots ?exists ~appname ~mode =
    Internal.getfiles ?roots ?exists ~appname ~mode (user, None)
end
