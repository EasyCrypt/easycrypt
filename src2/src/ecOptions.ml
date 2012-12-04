(* -------------------------------------------------------------------- *)
type options = {
  o_input : string option;
  o_idirs : string list;
}

(* -------------------------------------------------------------------- *)
let initial = {
  o_input = None;
  o_idirs = [];
}

(* -------------------------------------------------------------------- *)
let add_idir (options : options) (idir : string) =
  { options with o_idirs = idir :: options.o_idirs }

(* -------------------------------------------------------------------- *)
let specs () =
  let options = ref initial in
  let specs   =
    let add_idir  idir  = options := add_idir !options idir in
      [ "-I", Arg.String add_idir, "Add <dir> to the list of include directories" ]
  and set_input input =
    options := { !options with o_input = Some input }
  in

    fun () ->
      Arg.parse specs set_input ""; !options

(* -------------------------------------------------------------------- *)
let parse = specs ()
