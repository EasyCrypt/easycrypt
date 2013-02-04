(* -------------------------------------------------------------------- *)
type options = {
  o_input : string option;
  o_idirs : string list;
  o_emacs : bool;
}

(* -------------------------------------------------------------------- *)
let options = ref {
  o_input = None;
  o_idirs = [];
  o_emacs = false;
}

(* -------------------------------------------------------------------- *)
let specs () =
  let idirs = ref []
  and input = ref None
  and emacs = ref false in

  let add_idir  x = idirs := x :: !idirs
  and set_input x = input := Some x in

  let specs =
      [ "-I"    , Arg.String add_idir, "Add <dir> to the list of include directories";
        "-emacs", Arg.Set    emacs   , "Output format set to <emacs>"; ]
  in
    fun () ->
      Arg.parse specs set_input "";
      { o_input = !input;
        o_idirs = List.rev !idirs;
        o_emacs = !emacs; }

(* -------------------------------------------------------------------- *)
let parse = specs ()
