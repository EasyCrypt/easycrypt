(* -------------------------------------------------------------------- *)
open EcParsetree
open EcTypes
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_kill  : bool option -> codepos -> int option -> backward
val t_alias : bool option -> codepos -> psymbol option -> backward
val t_set   : bool option -> codepos -> bool * psymbol -> expr -> backward
val t_cfold : bool option -> codepos -> int option -> backward

(* -------------------------------------------------------------------- *)
val process_kill  : bool option * codepos * int option -> backward
val process_alias : bool option * codepos * psymbol option -> backward
val process_set   : bool option * codepos * bool * psymbol * pexpr -> backward
val process_cfold : bool option * codepos * int option -> backward
