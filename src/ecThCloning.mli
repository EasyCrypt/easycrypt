(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcEnv

(* -------------------------------------------------------------------- *)
val clone : EcEnv.env -> theory_cloning -> symbol * ctheory_w3
