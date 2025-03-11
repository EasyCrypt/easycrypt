(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst
open EcEnv
open EcMatching

(* -------------------------------------------------------------------- *)
type instance = {
  relation : path * ty list;
  params   : form list;
}

(* -------------------------------------------------------------------- *)
val as_instance : env -> (path * ty list) * form list -> (instance * form pair) option

(* -------------------------------------------------------------------- *)
val valid_setoid_context : env -> instance -> FPosition.ctxt -> bool
