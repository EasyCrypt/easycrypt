(** This file defines the commands available for the users in 'ocaml' mode. *)

open EcUtil
open ApiUtil

let _ = add {
  name = "withproof";
  args = [];
  help = help_of_string "Switch on/off proof checking mode"
}

let withproof = Global.change_withproof

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add {
  name = "help";
  args = [];
  help = help_of_string "Show this message"
}
let help () =
  Format.printf "@.";
  Format.printf "The following interactive commands are provided:@.";
  pp_cmds true (List.rev !cmds);
  Format.printf "@."

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "help_cmd"; args = ["cmd_name_or_part_of_it_or_reg_exp"];
              help = fun fmt _ -> Format.fprintf fmt
                "Search for matching commands.@,\
        If there is only one, show the help message for it.@,\
        Otherwise, show the list of matching commands."
            }
let help_cmd str =
  let regexp = Str.regexp str
  in let cmd_ok cmd =
       try let _ = Str.search_forward regexp cmd.name 0 in true
       with Not_found -> false
     in let liste = List.filter cmd_ok !cmds
        in let (liste,help) =
             match liste with
               | [] -> 
                 print_endline ("Sorry: found no command matching '"^str^"'");
                 ([],false)
               | _::[] -> (liste,true)
               | _     -> 
                 let egal_str cmd = (str = cmd.name)
                 in try let cmd = List.find egal_str liste in (cmd :: [], true)
                   with Not_found -> (liste,false)
           in pp_cmds help liste

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "set_debug"; args = ["debug_level"];
              help = fun fmt _ -> Format.fprintf fmt
                "Set debug level (0 to turn off debugging)."
            }
let set_debug x = EcUtil.set_debug x
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "set_prover"; args = ["prover_name"];
              help = fun fmt _ -> Format.fprintf fmt
                "Set default SMT."
            }
let set_prover name = WhyCmds.set_prover_option name
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "parse"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Switch to 'parsing' mode. @,\
        Use Drop;; or Ctrl-D to switch back to 'ocaml' mode"
            }
let parse () =
  Format.printf "@.\t@[ This is the 'parsing' mode. @,\
    Use Drop;; or Ctrl-D to switch to 'ocaml' mode@]@.@.";
  EcCommand.parse ();
  Format.printf "@.\t@[ End of 'parsing' mode.@]@."

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "emacs_parse"; args = [];
              help = fun _ _ -> ()}

let emacs_parse () =
  EcCommand.emacs_parse ()

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "parse_file"; args = ["filename.ec"];
              help = help_of_string
    "Parse given file"
            }
let parse_file src =
  EcCommand.parse_file src

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "parse_files"; args = ["filename.ec"];
              help = help_of_string
    "Parse given files"
            }
let parse_files src =
  EcCommand.parse_files src

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "quit"; args = [];
              help = help_of_string "Quit (you can also use ctrl-D)"
            }
let quit () = Format.printf "Bye bye !@."; exit 0
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "add_prop"; args = ["\"equiv_property_string\""];
              help = help_of_string "Add given property as current goal"
            }
let add_prop str =
  try
    let name, equiv = EcCommand.parse_equiv str in 
    EcStrategy.open_equiv name equiv
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "pp_state"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Show list of properties.@ @,\
        The current property is marked with a '>'"
            }

(*
  let pp_state () = assert false
(* Format.printf "%a" EcDeriv.pp_global_state () *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_prop"; args = ["prop_name"];
  help = help_of_string "Show named property"
  }
  let pp_prop _n = assert false
(*
  try Format.printf "%a" EcDeriv.pp_named_prop n
  with e -> catch_exn e
*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_n_prop"; args = ["num_prop"];
  help = help_of_string "Show property numbered 'num_prop' in [pp_state()]"
  }
  let pp_n_prop _n = assert false
(*
  try Format.printf "%a" EcDeriv.pp_n_prop n
  with e -> catch_exn e
*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_cur_prop"; args = [];
  help = help_of_string "Show current property"
  }
  let pp_cur_prop () = assert false
(*
  try Format.printf "%a" EcDeriv.pp_cur_prop ()
  with e -> catch_exn e
*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_n_prop_proof"; args = ["num_prop"];
  help = fun fmt _ -> Format.fprintf fmt
  "Show proof state of the property numbered 'num_prop'"
  }
  let pp_n_prop_proof n =
  try Format.printf "%a" EcDeriv.pp_n_prop_proof n
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_prop_proof"; args = ["prop_name"];
  help = fun fmt _ -> Format.fprintf fmt
  "Show proof state of the named property"
  }
  let pp_prop_proof n =
  try Format.printf "%a" EcDeriv.pp_named_prop_proof n
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
  let _ = add { name = "pp_cur_prop_proof"; args = [];
  help = fun fmt _ -> Format.fprintf fmt
  "Show proof state of the current property"
  }
  let pp_cur_prop_proof () =
  try Format.printf "%a" EcDeriv.pp_cur_prop_proof ()
  with e -> catch_exn e
*)

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "pp_goal"; args = [];
              help = help_of_string
    "Show current goal (first subgoal of current property)"
            }
let pp_goal () =
  try Format.printf "%a" EcDeriv.pp_cur_goal true
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "pg_inline"; args = ["side"];
              help = fun fmt _ -> Format.fprintf fmt
                "Inline last procedure call(s) in [side] program(s)"
            }

let pg_inline_exn _side =
  not_implemented "Api:pg_inline"
 (*
  let info = AstLogic.INLside (side, AstLogic.IKlast)
    (* AskB: what is IKlast ??? *) in
  EcCommand.process_tac EcUtil.dummy_pos (AstLogic.Tinline info) *)
let pg_inline side = try pg_inline_exn side with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let _ = add { name = "pg_sort"; args = ["side"];
              help = fun fmt _ -> Format.fprintf fmt
                "Try to sort statements in [side] program(s)"
            }
let pg_sort_exn side =
  let _ = EcDeriv.cur_tac (EcStrategy.sort_tac side) in ()

let pg_sort side = try pg_sort_exn side with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let _ = add { name = "pg_auto_rnd"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Try to heuristically apply rules for random assignments"
            }
let pg_auto_rnd_exn () =
  ignore (EcDeriv.cur_tac (EcDeriv.repeat_tac EcStrategy.auto_rnd_tac))

let pg_auto_rnd () = try pg_auto_rnd_exn () with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let _ = add { name = "pg_auto_fct"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Try to prove goal heuristically"
            }
let pg_auto_fct_exn () =
  let on_both _f1 _f2 = EcDeriv.fail_tac "on_both_call" in
  ignore (EcDeriv.cur_tac (EcStrategy.gen_wp_fct_body on_both))

let pg_auto_fct () = try pg_auto_fct_exn () with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "pg_derandomize"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Try to hoist random assignments in both programs"
            }
let pg_derandomize () =
  not_implemented "Api:pg_derandomize"
(*
  try EcCommand.process_tac EcUtil.dummy_pos (AstLogic.Tderandomize)
  with e -> catch_exn e
*)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "wp_asgn"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Compute relational WP of straightline deterministic code"
            }
let wp_asgn () =
  try EcCommand.process_tac EcUtil.dummy_pos (AstLogic.Tasgn)
  with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { 
  name = "wp_simpl"; args = [];
  help = fun fmt _ -> Format.fprintf fmt
    "Propagate postcondition in both programs and process assignments and conditionals (when possible)"
}

let wp_simpl () =
  try ignore (EcDeriv.cur_tac EcDeriv.wp_simpl_tac) with e -> catch_exn e

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "wp_rnd"; args = ["rnd_info"];
              help = fun fmt _ -> Format.fprintf fmt
                "Compute relational WP of random assignments"
(* TODO: add more help about [rnd_info] *)
            }
let wp_rnd info =
  try
    let info = EcCommand.parse_rnd_info info in
    EcCommand.process_tac EcUtil.dummy_pos (AstLogic.Trnd (AstLogic.Backwards,info))
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let _ = add { name = "tac_prove"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Try to prove goal using the current SMT.@,\
          Precondition: the list of statements in both programs must be empty"
            }
let tac_prove () =
  try ignore (EcDeriv.cur_tac EcStrategy.prove_tac)
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

let _ = add { name = "save_init_state"; args = [];
              help = fun fmt _ -> Format.fprintf fmt
                "Save the state after easycrypt_base"
            }
let save_init_state () =
  try
    Global.save_init_global ()
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
let parse_file_ep src =
  try
    PpLatex.parse_file src;
  with e -> catch_exn e
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
