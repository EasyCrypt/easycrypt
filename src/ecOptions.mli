(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
val parse_cmdline : string array -> options
