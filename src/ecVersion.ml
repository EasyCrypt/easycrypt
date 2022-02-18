(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2021 - Inria
 * Copyright (c) - 2012--2021 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
let copyright = [
  "Copyright (c) - 2012-2016 - IMDEA Software Institute";
  "Copyright (c) - 2012-2021 - Inria";
  "Copyright (c) - 2017-2021 - Ecole Polytechnique";
]

let url  = "https://www.easycrypt.info/"
let app  = "easycrypt"

module License = struct
  let engine = "Distributed under the terms of the CeCILL-C license"
  let stdlib = "Distributed under the terms of the CeCILL-B license"
end

let hash =
  match Build_info.V1.version () with
  | None   -> "n/a"
  | Some v -> Build_info.V1.Version.to_string v
