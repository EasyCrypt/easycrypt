(* Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-B license *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type command = [
| `Compile of cmp_option
| `Cli     of cli_option
| `Config
]

and options = {
  o_options : glb_options;
  o_command : command;
}

and cmp_option = {
  cmpo_input   : string;
  cmpo_provers : prv_options;
}

and cli_option = {
  clio_emacs   : bool;
  clio_provers : prv_options;
}

and prv_options = {
  prvo_maxjobs  : int;
  prvo_timeout  : int;
  prvo_provers  : string list option;
  pvro_checkall : bool;
  pvro_weakchk  : bool;
}

and ldr_options = {
  ldro_idirs : string list;
  ldro_rdirs : string list;
  ldro_boot  : bool;
}

and glb_options = {
  o_why3   : string option;
  o_loader : ldr_options;
}

(* -------------------------------------------------------------------- *)
type xoptions = {
  xp_globals  : xspec list;
  xp_commands : (string * string * xspec list) list;
  xp_groups   : (string * string * xspec list) list
}

and xspec = [
  | `Spec  of string * xkind * string
  | `Group of string
]

and xkind = [ `Flag | `Int | `String ]

type xvalue = [ `Bool of bool | `Int of int | `String of string ]

(* -------------------------------------------------------------------- *)
let print_usage ?progname ?(out = stderr) ?msg specs =
  let progname = odfl Sys.argv.(0) progname in

  let rec ccspecs hashelp specs =
    let for1 = function
      | `Spec (name, kind, help) ->
        let kind =
          match kind with
          | `Flag   -> Arg.Unit   (fun _ -> assert false)
          | `Int    -> Arg.Int    (fun _ -> assert false)
          | `String -> Arg.String (fun _ -> assert false)
        in
          Some ("-" ^ name, kind, " " ^ help)
      | `Group _ -> None
    in

    let specs = Arg.align (List.pmap for1 specs) in
      match hashelp with
      | true  -> specs
      | false -> List.filter (fun (x, _, _) -> not (String.endswith "-help" x)) specs

  and ccgroups specs =
    List.pmap (function `Group x -> Some x | _ -> None) specs
  in
    msg |> oiter (fun msg -> Printf.fprintf out "Error: %s\n\n%!" msg);
    Printf.fprintf out "Usage: %s [command] [options...] [args...]\n" progname;

    if specs.xp_groups <> [] then begin
      Printf.fprintf out "\n%!";
      Printf.fprintf out "* Available commands: %s\n%!"
        (String.concat ", "
           (List.map (fun (x, _, _) -> x) specs.xp_commands))
    end;

    let print_group hashelp head specs =
      let specs  = ccspecs hashelp specs
      and groups = ccgroups specs in
        Printf.fprintf out "\n%!";
        Printf.fprintf out "* %s\n%!" head;
        if specs <> [] then begin
          Printf.fprintf out "\n%!";
          List.iter
            (fun (name, _, help) ->
              Printf.fprintf out "  %s %s\n%!" name help)
            specs
        end;
        if groups <> [] then begin
          Printf.fprintf out "\n%!";
          Printf.fprintf out
            "  + any option of the following groups: %s\n%!"
            (String.concat ", " groups)
        end
    in

    print_group true "Global options" specs.xp_globals;

    List.iter (fun (name, help, specs) ->
      let head = Printf.sprintf "[%s] (%s)" name help in
        print_group false head specs)
      specs.xp_commands;

    List.iter (fun (name, help, specs) ->
      let head = Printf.sprintf "group [%s] (%s)" name help in
        print_group false head specs)
      specs.xp_groups

let parse spec argv =
  let error fmt = Printf.ksprintf (fun s -> raise (Arg.Bad s)) fmt in

  let groups =
    let cc1 = fun (name, _, specs) -> (name, specs) in
      Mstr.of_list (List.map cc1 spec.xp_groups)
  in

  let rec ccspec = function
    | `Spec (name, kind, help) -> [name, kind, help]
    | `Group name ->
        let group = oget (Mstr.find_opt name groups) in
          List.flatten (List.map ccspec group)
  in

  if (Array.length argv - 1 < 1) then
    raise (error "command expected");

  let command = argv.(1) in

  match List.findopt (fun (x, _, _) -> x = command) spec.xp_commands with
  | None -> raise (error "unknown command: %s" command);
  | Some (_, _, csp) -> begin
      let csp = List.flatten (List.map ccspec (spec.xp_globals @ csp)) in

      let values  = ref Mstr.empty in
      let anons   = ref [] in
      let current = ref 0 in

      let csp =
        let for1 (name, kind, help) =
          let set = fun v ->
            values := Mstr.change
              (fun vs -> Some (v :: (odfl [] vs)))
              name !values
          in

          let setter =
            match kind with
            | `Flag   -> Arg.Unit   (fun _ -> set (`Bool   true))
            | `Int    -> Arg.Int    (fun i -> set (`Int    i))
            | `String -> Arg.String (fun s -> set (`String s))
          in
            ("-" ^ name, setter, help)
        in
          List.map for1 csp
      in

      let argv =
        Array.init
          (Array.length argv - 1)
          (function 0 -> argv.(0) | i -> argv.(i+1))
      in
        begin
          try
            Arg.parse_argv ~current argv csp
              (fun anon -> anons := anon :: !anons)
              ""
          with Arg.Bad msg ->
            try
              ignore (Str.search_forward (Str.regexp "\\(.*\\)") msg 0);
              raise (Arg.Bad (Str.matched_group 1 msg))
            with Not_found -> raise (Arg.Bad msg)
        end;
        (command, !values, List.rev !anons)
  end

(* -------------------------------------------------------------------- *)
let specs = {
  xp_globals  = [
    `Spec  ("why3", `String, "why3 configuration file");
    `Group "loader";
  ];
  xp_commands = [

    ("compile", "Check an EasyCrypt file", [
      `Group "loader";
      `Group "provers"]);

    ("cli", "Run EasyCrypt top-level", [
      `Group "loader";
      `Group "provers";
      `Spec  ("emacs", `Flag, "Output format set to <emacs>")]);

    ("config", "Print EasyCrypt configuration", [])
  ];

  xp_groups = [
    ("provers", "Options related to provers", [
      `Spec ("p"          , `String, "Add a prover to the set of provers");
      `Spec ("max-provers", `Int   , "Maximum number of prover running in the same time");
      `Spec ("timeout"    , `Int   , "Set the SMT timeout");
      `Spec ("check-all"  , `Flag  , "Force checking all files");
      `Spec ("weak-check" , `Flag  , "Start prover in weak check mode")]);

    ("loader", "Options related to loader", [
      `Spec ("I"   , `String, "Add <dir> to the list of include directories");
      `Spec ("R"   , `String, "Recursively add <dir> to the list of include directories");
      `Spec ("boot", `Flag  , "Don't load prelude")])
  ]
}

(* -------------------------------------------------------------------- *)
let get_string name values =
  match Mstr.find_opt name values with
  | None -> None
  | Some (`String x :: _) -> Some x
  | _ -> assert false

let get_flag name values =
  match Mstr.find_opt name values with
  | None -> false
  | Some (`Bool b :: _) -> b
  | _ -> assert false

let get_int name values =
  match Mstr.find_opt name values with
  | None -> None
  | Some (`Int i :: _) -> Some i
  | _ -> assert false

let get_strings name values =
  let xs = odfl [] (Mstr.find_opt name values) in
  let xs = List.map (function `String x -> x | _ -> assert false) xs in
    List.rev xs

(* -------------------------------------------------------------------- *)
let ldr_options_of_values values =
  { ldro_idirs = get_strings "I"    values;
    ldro_rdirs = get_strings "R"    values;
    ldro_boot  = get_flag    "boot" values; }

let glb_options_of_values values =
  { o_why3   = get_string "why3" values;
    o_loader = ldr_options_of_values values; }

let prv_options_of_values values =
  let provers =
    match get_strings "p" values with
    | [] -> None | provers -> Some provers
  in
    { prvo_maxjobs  = odfl 4 (get_int "max-provers" values);
      prvo_timeout  = odfl 3 (get_int "timeout" values);
      prvo_provers  = provers;
      pvro_checkall = get_flag "check-all" values;
      pvro_weakchk  = get_flag "weak-check" values; }

let cli_options_of_values values =
  { clio_emacs   = get_flag "emacs" values;
    clio_provers = prv_options_of_values values; }

let cmp_options_of_values values input =
  { cmpo_input   = input;
    cmpo_provers = prv_options_of_values values; }

(* -------------------------------------------------------------------- *)
let parse argv =
  let (command, values, anons) = parse specs argv in
  let command =
    match command with
    | "compile" -> begin
        match anons with
        | [input] -> `Compile (cmp_options_of_values values input)
        | _ -> raise (Arg.Bad "this command takes a single argument")
    end

    | "cli" ->
        if anons != [] then
          raise (Arg.Bad "this command does not take arguments");
        `Cli (cli_options_of_values values)

    | "config" ->
        if anons != [] then
          raise (Arg.Bad "this command does not take arguments");
        `Config

    | _ -> assert false
  in
    { o_options = glb_options_of_values values;
      o_command = command; }

(* -------------------------------------------------------------------- *)
let parse argv =
  let args   = Array.sub argv 1 (Array.length argv - 1) in
  let hascmd =
    match args with
    | [||] -> false
    | _    -> List.exists (fun (x, _, _) -> x = args.(0)) specs.xp_commands
  in

  let isec     = fun x -> String.endswith ".ec" x in
  let necfiles = Array.fold_left (fun s n -> if isec  n then s+1 else s) 0 args in
  let ecommand =
    match hascmd with
    | true -> None
    | false when necfiles > 0 -> Some "compile"
    | false -> Some "cli"
  in

  let argv =
    match ecommand with
    | None     -> Array.copy argv
    | Some cmd ->
      Array.init
        (Array.length argv + 1)
        (function
         | 0 -> argv.(0)
         | 1 -> cmd
         | i -> argv.(i-1))
  in
    try parse argv
    with
    | Arg.Bad  msg -> print_usage ~msg specs; exit 1
    | Arg.Help _   -> print_usage specs; exit 1
