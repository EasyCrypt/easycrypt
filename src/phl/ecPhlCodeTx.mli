(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_kill  : oside -> codepos -> int option -> backward
val t_alias : oside -> codepos -> psymbol option -> backward
val t_set   : oside -> codepos -> bool * psymbol -> expr -> backward
val t_cfold : oside -> codepos -> int option -> backward

(* -------------------------------------------------------------------- *)
val process_kill  : oside * codepos * int option -> backward
val process_alias : oside * codepos * psymbol option -> backward
val process_set   : oside * codepos * bool * psymbol * pexpr -> backward
val process_cfold : oside * codepos * int option -> backward
val process_case  : oside * codepos -> backward

(* -------------------------------------------------------------------- *)
val process_weakmem : (oside * psymbol * fun_params) -> backward
