
(** {2 Type safe soft constructors} *)

type c_tyexpr = tyexpr

let ce_type (e : tyexpr) =
  (oget e.tye_meta).tym_type

let ce_meta ty e : c_tyexpr =
  { tye_meta = Some { tym_type = ty };
    tye_desc = e; }

let ce_local (env : env) (x : EcIdent.t) =
  (* Je pense que c'est pas une bonne idee d'avoir ce path on devrait
     avoir Pident x, je n'aime pas que le path depend du scope *)
  let xpath = EcPath.Pqname (env.env_scope, x) in
  let xty   = Var.lookup_by_path xpath env in
    if xty.vb_kind <> None then assert false;
    ce_meta xty.vb_type (Elocal x)

let ce_var (env : env) (p : prog_var) =
  let xty = Var.lookup_by_path p.pv_name env in
    if xty.vb_kind = None then assert false;
    ce_meta xty.vb_type (Evar p)

let ce_int (_env : env) (i : int) =
  ce_meta tint (Eint i)

let ce_tuple (_env : env) es =
  ce_meta
    (Ttuple (List.map ce_type es))
    (Etuple es)

let ce_let (_env : env) p e1 e2 =
  ce_meta (ce_type e2) (Elet (p, e1, e2))

let ce_if (env : env) c e1 e2 =
  check_type env (ce_type c) tbool;
  check_type env (ce_type e1) (ce_type e2);
  ce_meta (ce_type e1) (Eif (c, e1, e2))

let ce_app (_env : env) _p _e _ty =
  assert false                          (* FIXME *)
