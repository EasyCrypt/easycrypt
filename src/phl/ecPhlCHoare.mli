open EcFol
open EcSymbols
open EcPath
open EcCoreGoal

val choare_modapply_args :
  tcenv1 ->
  EcIdent.t -> mpath -> form ->
  (symbol * EcParsetree.pcost) list ->
  form
