(* -------------------------------------------------------------------- *)
type command = [
  | `Compile of cmp_option
  | `Cli     of cli_option
  | `Config
  | `Runtest of run_option
  | `Why3Config
  | `DocGen of doc_option
  | `Llm of llm_option
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

and llm_option = {
  llmo_provers   : prv_options;
  llmo_help      : bool;
  llmo_eval      : string option;
}

and prv_options = {
  prvo_maxjobs    : int option;
  prvo_timeout    : int option;
  prvo_cpufactor  : int option;
  prvo_provers    : string list option;
  prvo_quorum     : int option;
  prvo_pragmas    : string list;
  prvo_ppwidth    : int option;
  prvo_checkall   : bool;
  prvo_profile    : bool;
  prvo_why3server : string option;
}

and ldr_options = {
  ldro_idirs  : (string option * string * bool) list;
  ldro_boot   : bool;
  ldro_stdlib : string list;
    (* When non-empty, these directories replace the built-in
       [Sites.theories] for prelude and recursive-System namespace
       loading. Empty means "use the built-in stdlib". *)
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
  ini_quorum   : int option;
  ini_timeout  : int option;
  ini_idirs    : (string option * string) list;
  ini_rdirs    : (string option * string) list;
  ini_pragmas  : string list;
}

type ini_context = {
  inic_ini  : ini_options;
  inic_root : string option;
}

(* -------------------------------------------------------------------- *)
exception InvalidIniFile of (int * string)

val read_ini_file : string -> ini_options

(* -------------------------------------------------------------------- *)
(* Overlay project INI settings discovered at run time (e.g. by the LLM
   REPL's [LOAD]) on top of already-parsed prover options, mirroring
   the precedence of option parsing with a known project file. *)
val prv_options_with_ini : ini_context list -> prv_options -> prv_options

(* The load path contributed by INI contexts, in [ldro_idirs] shape:
   (namespace, dir, recursive). *)
val ini_loadpath : ini_context list -> (string option * string * bool) list

val parse_cmdline :
     ?ini:(string option -> ini_context list)
  -> string array
  -> options
