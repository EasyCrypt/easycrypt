(* -------------------------------------------------------------------- *)
open EcUtils
open EcAst
open EcModules
open EcTypes
open EcFol

(* -------------------------------------------------------------------- *)
type match_branch = {
  mb_mem  : memenv;
  mb_cond : ss_inv;
  mb_body : stmt;
}

(* -------------------------------------------------------------------- *)
let match_branches env me e bs =
  let typ, tydc, tyinst = oget (EcEnv.Ty.get_top_decl e.e_ty env) in
  let tyd = oget (EcDecl.tydecl_as_datatype tydc) in
  let f   = ss_inv_of_expr (fst me) e in

  let branch (cname, _) (cvars, body) =
    let cname = EcPath.pqoname (EcPath.prefix typ) cname in

    let mb_mem, pvs =
      let ovs =
        List.map
          (fun (x, xty) -> { ov_name = Some (EcIdent.name x); ov_type = xty; })
          cvars in
      EcMemory.bindall_fresh ovs me in

    let subst, pvs =
      List.fold_left_map (fun s ((x, xty), ov) ->
          let pv = pv_loc (oget ov.ov_name) in
          (bind_elocal s x (e_var pv xty), (pv, xty)))
        Fsubst.f_subst_id (List.combine cvars pvs) in

    (* NB: the constructor is given the datatype as type, as before the
       migration (behaviour preserved). *)
    let mb_cond =
      let vars = List.map (fun (pv, ty) -> f_pvar pv ty (fst mb_mem)) pvs in
      let cop  = f_op cname tyinst f.inv.f_ty in
      let cop  = map_ss_inv ~m:f.m (fun vs -> f_app cop vs f.inv.f_ty) vars in
      map_ss_inv2 f_eq f cop in

    { mb_mem; mb_cond; mb_body = s_subst subst body; }
  in

  List.map2 branch tyd.tydt_ctors bs
