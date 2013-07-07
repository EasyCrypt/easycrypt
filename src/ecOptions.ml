(* -------------------------------------------------------------------- *)
open EcUtils

(* -------------------------------------------------------------------- *)
type options = {
  o_input      : string option;
  o_idirs      : string list;
  o_boot       : bool;
  o_emacs      : bool;
  o_why3       : string option;
  o_full_check : bool;
  o_max_prover : int;
  o_provers    : string list option;
}

(* -------------------------------------------------------------------- *)
let options = ref {
  o_input      = None;
  o_idirs      = [];
  o_boot       = false;
  o_emacs      = false;
  o_why3       = None;
  o_full_check = false;
  o_max_prover = 4;
  o_provers    = None;
}

(* -------------------------------------------------------------------- *)
let specs () =
  let idirs       = ref []
  and boot        = ref false
  and input       = ref None
  and emacs       = ref false
  and why3        = ref None 
  and full_check  = ref false 
  and max_provers = ref 4
  and provers     = ref [] in

  let add_idir    x = idirs := x :: !idirs
  and set_why3    x = why3  := Some x
  and set_max     x = max_provers := x
  and set_provers x = provers := x :: !provers

  and set_input x =
    if !input <> None then
      raise (Arg.Bad "you must give at most on EasyCrypt file");
    input := Some x
  in

  let specs =
      [ "-I"          , Arg.String add_idir   , "Add <dir> to the list of include directories";
        "-boot"       , Arg.Set    boot       , "Don't load prelude";
        "-emacs"      , Arg.Set    emacs      , "Output format set to <emacs>";
        "-why3"       , Arg.String set_why3   , "Load why3 configuration from given files";
        "-full_check" , Arg.Set    full_check , "Check every loaded file, disable checkproof off";
        "-max_provers", Arg.Int    set_max    , "Maximum number of prover running in the same time";
        "-p"          , Arg.String set_provers, "Add a prover to the set of provers"
      ] in
  let specs = Arg.align (List.map (fun (x, o, d) -> (x, o, " " ^ d)) specs) in

    fun () ->
      Arg.parse specs set_input "";
      let provers = if !provers = [] then None else Some !provers in

      { o_input      = !input;
        o_boot       = !boot;
        o_idirs      = List.rev !idirs;
        o_emacs      = !emacs;
        o_why3       = !why3;
        o_full_check = !full_check;
        o_max_prover = !max_provers;
        o_provers    = provers;
      }

(* -------------------------------------------------------------------- *)
let parse = specs ()
