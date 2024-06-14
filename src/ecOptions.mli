(* -------------------------------------------------------------------- *)
type command = [
  | `Compile of cmp_option
  | `Cli     of cli_option
  | `Config
  | `Runtest of run_option
  | `Why3Config
  | `DocGen of doc_option
]

and options = {
  o_options : glb_options;
  o_command : command;
}

and cmp_option = {
  cmpo_input   : string;
  cmpo_provers : prv_options;
  cmpo_gcstats : bool;
  cmpo_compact : int option;
  cmpo_tstats  : string option;
  cmpo_noeco   : bool;
  cmpo_script  : bool;
  cmpo_trace   : bool;
}

and cli_option = {
  clio_emacs   : bool;
  clio_provers : prv_options;
}

and run_option = {
  runo_input     : string;
  runo_scenarios : string list;
  runo_report    : string option;
  runo_provers   : prv_options;
  runo_jobs      : int option;
  runo_rawargs   : string list;
}

and doc_option = {
  doco_input     : string;
  doco_outdirp   : string option;
}

and prv_options = {
  prvo_maxjobs    : int option;
  prvo_timeout    : int option;
  prvo_cpufactor  : int option;
  prvo_provers    : string list option;
  prvo_pragmas    : string list;
  prvo_ppwidth    : int option;
  prvo_checkall   : bool;
  prvo_profile    : bool;
  prvo_iterate    : bool;
  prvo_why3server : string option;
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
  ini_timeout  : int option;
  ini_idirs    : (string option * string) list;
  ini_rdirs    : (string option * string) list;
}

type ini_context = {
  inic_ini  : ini_options;
  inic_root : string option;
}

(* -------------------------------------------------------------------- *)
exception InvalidIniFile of (int * string)

val read_ini_file : string -> ini_options

val parse_cmdline :
     ?ini:(string option -> ini_context list)
  -> string array
  -> options
