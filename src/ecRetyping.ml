(* -------------------------------------------------------------------- *)
open EcTypes
open EcTypesmod
open EcEnv

(* -------------------------------------------------------------------- *)
let rec re_expr (env : env) (epolicy : epolicy) (e : tyexpr) =
  match e.tys_desc with
  | Eint i ->
      ce_int env i

  | Eflip ->
      ce_flip env

  | Einter (e1, e2) ->
      let e1 = expr env epolicy e1 in
      let e2 = expr env epolicy e2 in
        ce_inter env e1 e2

  | Eexcepted (e1, e2) ->
      let e1 = expr env epolicy e1 in
      let e2 = expr env epolicy e2 in
        ce_excepted env e1 e2

  | Elocal (x, ty) ->
      let ty = re_type env ty in
        ce_local env x ty

  | Evar (x, ty) ->
      let ty = re_type env ty in
        ce_var x ty

  | Eapp (p, es, ty) ->
      let es = List.map (re_expr env epolicy) es in
      let ty = re_type ty in
        ce_app (p, es, ty)

  | Elet (p, e1, e2) ->
      let e1 = re_expr env epolicy e1 in
      let e2 = re_expr env epolicy e2 in
        ce_let (p, e1, e2)

  | Etuple es ->
      let es = List.map (re_expr env epolicy) es in
        re_tuple env es

  | Eif (c, e1, e2) ->
      let c  = re_expr env epolicy c  in
      let e1 = re_expr env epolicy e1 in
      let e2 = re_expr env epolicy e2 in
        re_if env c e1 e2
