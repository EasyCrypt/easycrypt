(* -------------------------------------------------------------------- *)
type options = {
  o_input      : string option;
  o_idirs      : string list;
  o_emacs      : bool;
  o_why3       : string option;
  o_full_check : bool;
}

(* -------------------------------------------------------------------- *)
let options = ref {
  o_input      = None;
  o_idirs      = [];
  o_emacs      = false;
  o_why3       = None;
  o_full_check = false;
}

(* -------------------------------------------------------------------- *)
let specs () =
  let idirs = ref []
  and input = ref None
  and emacs = ref false
  and why3  = ref None 
  and full_check = ref false in

  let add_idir  x = idirs := x :: !idirs
  and set_why3  x = why3  := Some x
  and set_input x = input := Some x in

  let specs =
      [ "-I"    , Arg.String add_idir, "Add <dir> to the list of include directories";
        "-emacs", Arg.Set    emacs   , "Output format set to <emacs>";
        "-why3" , Arg.String set_why3, "Load why3 configuration from given files";
        "-full_check", Arg.Set full_check, "Check every loaded file, disable checkproof off"
      ]
  in
    fun () ->
      Arg.parse specs set_input "";
      { o_input      = !input;
        o_idirs      = List.rev !idirs;
        o_emacs      = !emacs;
        o_why3       = !why3;
        o_full_check = !full_check;
      }

(* -------------------------------------------------------------------- *)
let parse = specs ()
