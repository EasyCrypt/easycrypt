(* -------------------------------------------------------------------- *)
open EcMaps

module Json = Yojson

(* -------------------------------------------------------------------- *)
module Version = struct
  let current : int = 2
end

(* -------------------------------------------------------------------- *)
type digest = Digest.t

type ecoroot = {
  eco_kind   : EcLoader.kind;
  eco_digest : digest;
}

type eco = {
  eco_root    : ecoroot;
  eco_depends : ecoroot Mstr.t;
}

(* -------------------------------------------------------------------- *)
exception InvalidEco

(* -------------------------------------------------------------------- *)
let kind_to_json (k:EcLoader.kind) =
  match k with
  | `Ec  -> `String "ec"
  | `EcA -> `String "eca"

let kind_of_json (data:Json.t) =
  match data with
  | `String "ec"  -> `Ec
  | `String "eca" -> `EcA
  | _ -> raise InvalidEco

(* -------------------------------------------------------------------- *)
let digest_of_json (data : Json.t) : Digest.t =
  match data with
  | `String x -> begin
      try  Digest.from_hex x
      with Invalid_argument _ -> raise InvalidEco
    end
  | _ -> raise InvalidEco

(* -------------------------------------------------------------------- *)
let digest_to_json (data : Digest.t) : Json.t =
  `String (Digest.to_hex data)

(* -------------------------------------------------------------------- *)
let namespace_of_json (date : Json.t) : string =
  match date with `String x -> x | _ -> raise InvalidEco

(* -------------------------------------------------------------------- *)
let ecoroot_to_json (ecor : ecoroot) : Json.t =
  `Assoc [
     "kind"     , kind_to_json ecor.eco_kind;
     "digest"   , digest_to_json ecor.eco_digest;
   ]

let ecoroot_of_json (data : Json.t) : ecoroot =
  match data with
  | `Assoc data ->
      let data = Mstr.of_list data in
      let kd = kind_of_json (Mstr.find_exn InvalidEco "kind" data) in
      let dg = digest_of_json (Mstr.find_exn InvalidEco "digest" data) in
      { eco_kind = kd; eco_digest = dg; }

  | _ -> raise InvalidEco

(* -------------------------------------------------------------------- *)
let depends_of_json (data : Json.t) : ecoroot Mstr.t =
  match data with
  | `Assoc data ->
      let data = List.map (EcUtils.snd_map ecoroot_of_json) data in
      Mstr.of_list data

  | _ ->
      raise InvalidEco

(* -------------------------------------------------------------------- *)
let to_json (eco : eco) : Json.t =
  let depends = Mstr.bindings (Mstr.map ecoroot_to_json eco.eco_depends) in

  `Assoc
    [ "version", `Int Version.current;
      "echash" , `String EcVersion.hash;
      "root"   , ecoroot_to_json eco.eco_root;
      "depends", `Assoc depends ]

(* -------------------------------------------------------------------- *)
let of_json (data : Json.t) : eco =
  match data with
  | `Assoc data ->
      let data    = Mstr.of_list data in
      let version = Mstr.find_exn InvalidEco "root" data in
      let echash  = Mstr.find_exn InvalidEco "echash" data in

      if version <> `Int Version.current then
        raise InvalidEco;

      if echash <> `String EcVersion.hash then
        raise InvalidEco;

      let root    = ecoroot_of_json (Mstr.find_exn InvalidEco "root" data) in
      let depends = depends_of_json (Mstr.find_exn InvalidEco "depends" data) in

      { eco_root = root; eco_depends = depends; }

  | _ -> raise InvalidEco

(* -------------------------------------------------------------------- *)
let pp (fmt : Format.formatter) (eco : eco) =
  Json.pretty_print fmt (to_json eco)

let of_file (filename : string) : eco =
  try  of_json ((Json.Basic.from_file filename :> Json.t))
  with Json.Json_error _ -> raise InvalidEco

(* ---------------------------------------------------------------------- *)
let check_eco loader filename =
  let module E = struct exception BadEco end in

  let check_digest filename ecor =
    if EcLoader.get_kind filename <> ecor.eco_kind then
      raise E.BadEco;
    if Digest.file filename <> ecor.eco_digest then
      raise E.BadEco
  in

  let nameo = Filename.remove_extension filename ^ ".eco" in

  try
    if not (Sys.file_exists nameo) then
      raise E.BadEco;

    let eco = of_file nameo in

    check_digest filename eco.eco_root;

    let doit name d =
      match loader name with
      | None ->
          raise E.BadEco
      | Some (_, filename, _) ->
          check_digest filename d

    in EcMaps.Mstr.iter doit eco.eco_depends; true

  with E.BadEco -> false
