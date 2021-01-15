(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
  cmpo_tstats  : string option;
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
  ldro_idirs : (string option * string * bool) list;
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
  ini_idirs    : (string option * string) list;
}

(* -------------------------------------------------------------------- *)
exception InvalidIniFile of (int * string)

val read_ini_file : string -> ini_options
val parse_cmdline : ?ini:ini_options -> string array -> options
