(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcMaps

(* -------------------------------------------------------------------- *)
type command = [
| `Compile of cmp_option
| `Cli     of cli_option
| `Config
| `Why3Config
]

and options = {
  o_options : glb_options;
  o_command : command;
}

and cmp_option = {
  cmpo_input   : string;
  cmpo_provers : prv_options;
  cmpo_gcstats : bool;
}

and cli_option = {
  clio_emacs   : bool;
  clio_provers : prv_options;
}

and prv_options = {
  prvo_maxjobs   : int;
  prvo_timeout   : int;
  prvo_cpufactor : int;
  prvo_provers   : string list option;
  prvo_pragmas   : string list;
  prvo_ppwidth   : int option;
  prvo_checkall  : bool;
  prvo_profile   : bool;
  prvo_iterate   : bool;
}

and ldr_options = {
  ldro_idirs : string list;
  ldro_rdirs : string list;
  ldro_boot  : bool;
}

and glb_options = {
  o_why3     : string option;
  o_reloc    : bool;
  o_ovrevict : string list;
  o_loader   : ldr_options;
}

(* -------------------------------------------------------------------- *)
type ini_options = {
  ini_ppwidth  : int option;
  ini_why3     : string option;
  ini_ovrevict : string list;
  ini_provers  : string list;
  ini_idirs    : string list;
  ini_rdirs    : string list;
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
      | false -> List.filter (fun (x, _, _) -> not (String.ends_with x "-help")) specs

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

  match List.ofind (fun (x, _, _) -> x = command) spec.xp_commands with
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
            let msg =
              EcRegexp.exec (`S "(.*)") msg
                |> omap (fun m -> oget (EcRegexp.Match.group m 1))
                |> odfl msg
            in raise (Arg.Bad msg)
        end;
        (command, !values, List.rev !anons)
  end

(* -------------------------------------------------------------------- *)
let specs = {
  xp_globals  = [
    `Spec  ("why3"    , `String, "why3 configuration file");
    `Spec  ("reloc"   , `Flag  , "<for internal use>");
    `Spec  ("no-evict", `String, "Don't evict given prover");

    `Group "loader";
  ];
  xp_commands = [

    ("compile", "Check an EasyCrypt file", [
      `Group "loader";
      `Group "provers";
      `Spec  ("gcstats", `Flag, "Display GC statistics")]);

    ("cli", "Run EasyCrypt top-level", [
      `Group "loader";
      `Group "provers";
      `Spec  ("emacs", `Flag, "Output format set to <emacs>")]);

    ("config", "Print EasyCrypt configuration", []);

    ("why3config", "Configure why3", []);
  ];

  xp_groups = [
    ("provers", "Options related to provers", [
      `Spec ("p"          , `String, "Add a prover to the set of provers");
      `Spec ("max-provers", `Int   , "Maximum number of prover running in the same time");
      `Spec ("timeout"    , `Int   , "Set the SMT timeout");
      `Spec ("cpu-factor" , `Int   , "Set the timeout CPU factor");
      `Spec ("check-all"  , `Flag  , "Force checking all files");
      `Spec ("pragmas"    , `String, "Comma-separated list of pragmas");
      `Spec ("pp-width"   , `Int   , "pretty-printing width");
      `Spec ("profile"    , `Flag  , "Collect some profiling informations");
      `Spec ("iterate"    , `Flag  , "Force to iterate smt call");
    ]);


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

let get_string_list name values : string list =
  let split x =
    let aout = List.map String.trim (String.nsplit x ",") in
    List.filter ((<>) "") aout
  in

  List.flatten (List.map
    (function `String x -> split x | _ -> assert false)
    (odfl [] (Mstr.find_opt name values)))

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
let ldr_options_of_values ?ini values =
  if get_flag "boot" values then
    { ldro_idirs = []; ldro_rdirs = []; ldro_boot = true; }
  else
    let idirs = omap_dfl (fun x -> x.ini_idirs) [] ini in
    let rdirs = omap_dfl (fun x -> x.ini_idirs) [] ini in
    { ldro_idirs = idirs @ (get_strings "I" values);
      ldro_rdirs = rdirs @ (get_strings "R" values);
      ldro_boot  = false; }

let glb_options_of_values ?ini values =
  let why3 =
    match get_string "why3" values with
    | None -> obind (fun x -> x.ini_why3) ini
    | why3 -> why3 in

  let ovrevict = omap_dfl (fun x -> x.ini_ovrevict) [] ini in

  { o_why3     = why3;
    o_reloc    = get_flag "reloc" values;
    o_ovrevict = ovrevict @ (get_strings "no-evict" values);
    o_loader   = ldr_options_of_values ?ini values; }

let prv_options_of_values ?ini values =
  let provers =
    let provers =
      (omap_dfl (fun x -> x.ini_provers) [] ini) @
      (get_strings "p" values)
    in match provers with [] -> None | provers -> Some provers
  in
    { prvo_maxjobs   = odfl 4 (get_int "max-provers" values);
      prvo_timeout   = odfl 3 (get_int "timeout" values);
      prvo_cpufactor = odfl 1 (get_int "cpu-factor" values);
      prvo_provers   = provers;
      prvo_pragmas   = get_string_list "pragmas" values;
      prvo_ppwidth   = begin
        match get_int "pp-width" values with
        | None -> obind (fun x -> x.ini_ppwidth) ini
        | Some i -> Some i
      end;
      prvo_checkall  = get_flag "check-all" values;
      prvo_profile   = get_flag "profile" values;
      prvo_iterate   = get_flag "iterate" values;
    }

let cli_options_of_values ?ini values =
  { clio_emacs   = get_flag "emacs" values;
    clio_provers = prv_options_of_values ?ini values; }

let cmp_options_of_values ?ini values input =
  { cmpo_input   = input;
    cmpo_provers = prv_options_of_values ?ini values;
    cmpo_gcstats = get_flag "gcstats" values; }

(* -------------------------------------------------------------------- *)
let parse ?ini argv =
  let (command, values, anons) = parse specs argv in
  let command =
    match command with
    | "compile" -> begin
        match anons with
        | [input] -> `Compile (cmp_options_of_values ?ini values input)
        | _ -> raise (Arg.Bad "this command takes a single argument")
    end

    | "cli" ->
        if anons != [] then
          raise (Arg.Bad "this command does not take arguments");
        `Cli (cli_options_of_values ?ini values)

    | "config" ->
        if anons != [] then
          raise (Arg.Bad "this command does not take arguments");
        `Config

    | "why3config" ->
        if anons != [] then
          raise (Arg.Bad "this command does not take arguments");
        `Why3Config

    | _ -> assert false
  in
    { o_options = glb_options_of_values ?ini values;
      o_command = command; }

(* -------------------------------------------------------------------- *)
let parse_cmdline ?ini argv =
  let args   = Array.sub argv 1 (Array.length argv - 1) in
  let hascmd =
    match args with
    | [||] -> false
    | _    -> List.exists (fun (x, _, _) -> x = args.(0)) specs.xp_commands
  in

  let isec x = EcRegexp.match_ (`S ".*\\.eca?") x in

  let necfiles =
    Array.fold_left
      (fun s n -> if isec n then s+1 else s) 0 args in

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
    try parse ?ini argv
    with
    | Arg.Bad  msg -> print_usage ~msg specs; exit 1
    | Arg.Help _   -> print_usage specs; exit 1

(* -------------------------------------------------------------------- *)
exception InvalidIniFile of (int * string)

let read_ini_file (filename : string) =
  let sec = "general" in
  let ini =
    try  new Inifiles.inifile filename
    with Inifiles.Ini_parse_error code -> raise (InvalidIniFile code) in

  let tryget name =
    try  Some (ini#getval sec name)
    with
    | Inifiles.Invalid_section _
    | Inifiles.Invalid_element _ -> None

  and tryint name =
    try  Some (int_of_string (ini#getval sec name))
    with
    | Inifiles.Invalid_section _
    | Inifiles.Invalid_element _
    | Failure _ -> None

  and trylist name =
    try  ini#getaval sec name
    with
    | Inifiles.Invalid_section _
    | Inifiles.Invalid_element _ -> [] in

  let expand (x : string) =
    EcRegexp.sub
      (`C (EcRegexp.regexp "^~"))
      (`S XDG.home) x in

  let ini =
    { ini_ppwidth  = tryint  "pp-width" ;
      ini_why3     = tryget  "why3conf";
      ini_ovrevict = trylist "no-evict";
      ini_provers  = trylist "provers" ;
      ini_idirs    = trylist "idirs"   ;
      ini_rdirs    = trylist "rdirs"   ; } in

  { ini_ppwidth  = ini.ini_ppwidth;
    ini_why3     = omap expand ini.ini_why3;
    ini_ovrevict = ini.ini_ovrevict;
    ini_provers  = ini.ini_provers;
    ini_idirs    = List.map expand ini.ini_idirs;
    ini_rdirs    = List.map expand ini.ini_rdirs; }
