(* -------------------------------------------------------------------- *)
open EcPath

(* -------------------------------------------------------------------- *)
let search (env : EcEnv.env) (paths : Sp.t) =
  let check ax =
    match ax.EcDecl.ax_spec with
    | None   -> false
    | Some f -> not (Sp.disjoint (EcFol.f_ops f) paths)

  in EcEnv.Ax.all ~check env;
