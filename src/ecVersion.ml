(* -------------------------------------------------------------------- *)
let copyright = [
  "Copyright (c) 2012 IMDEA Software Institute";
  "Copyright (c) 2012 Inria";
  "Copyright (c) 2017 Ecole Polytechnique";
  "Copyright (c) EasyCrypt contributors (see AUTHORS)";
]

let url  = "https://www.easycrypt.info/"
let app  = "easycrypt"

module License = struct
  let engine = "Distributed under the terms of the MIT license"
  let stdlib = "Distributed under the terms of the MIT license"
end

let hash =
  match Build_info.V1.version () with
  | None   -> "n/a"
  | Some v -> Build_info.V1.Version.to_string v
