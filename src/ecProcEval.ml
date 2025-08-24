(* -------------------------------------------------------------------- *)
open EcUtils
open EcPath
open EcAst

(* -------------------------------------------------------------------- *)
let eval (env : EcEnv.env) =
  let exception NotAValue in

  let hyps = EcEnv.LDecl.init env [] in
  let cbv  = EcCallbyValue.norm_cbv EcReduction.full_red hyps in 

  let rec get_function (fpath : xpath) =
    let fun_ = EcEnv.Fun.by_xpath fpath env in

    match fun_.f_def with
    | FBdef def -> fun_, def
    | FBalias alias -> let _, def = get_function alias in fun_, def
    | _ -> raise NotAValue in

  let rec is_literal (f : form) =
    match EcFol.sform_of_form f with
    | SFtrue | SFfalse | SFint _ -> true
    | SFtuple fs -> List.for_all is_literal fs
    | _ -> false in

  let eval (subst : EcPV.PVM.subst) (v : form) =
    let aout = cbv (EcPV.PVM.subst env subst v) in
    if not (is_literal aout) then raise NotAValue;
    aout in

  let rec doit (fpath : xpath) (args : form list) =
    let fun_, body = get_function fpath in
    let subst =
      List.fold_left2 (fun (subst : EcPV.PVM.subst) (var : ovariable) (arg : form) ->
        var.ov_name |> Option.fold ~none:subst ~some:(fun name ->
          let pv = EcTypes.pv_loc name in
          EcPV.PVM.add env pv mhr arg subst
        )
      ) EcPV.PVM.empty fun_.f_sig.fs_anames args in

    let subst = for_stmt subst body.f_body in

    Option.map
      (eval subst -| EcFol.form_of_expr mhr)
      body.f_ret
  
  and for_instr (subst : EcPV.PVM.subst) (instr : EcModules.instr) = 
    match instr.i_node with
    | Sasgn (lvalue, rvalue) -> begin
      let rvalue = eval subst (EcFol.form_of_expr mhr rvalue) in
      match lvalue with
      | LvVar (pv, _) ->
        EcPV.PVM.add env pv mhr rvalue subst
      | LvTuple pvs ->
        let rvalue = EcFol.destr_tuple rvalue in
        List.fold_left2 (fun subst (pv, _) rvalue ->
          EcPV.PVM.add env pv mhr rvalue subst
        ) subst pvs rvalue
    end

    | Scall (lv, f, args) -> begin
      let args = List.map (eval subst -| EcFol.form_of_expr mhr) args in
      let aout = doit f args in

      match lv with
      | None ->
        subst

      | Some (LvVar (pv, _)) ->
        EcPV.PVM.add env pv mhr (Option.get aout) subst

      | Some (LvTuple pvs) ->
        List.fold_left2 (fun subst (pv, _) aout ->
          EcPV.PVM.add env pv mhr aout subst
        ) subst pvs (EcFol.destr_tuple (Option.get aout))
    end

    | Sif (cond, strue, sfalse) ->
      let cond = eval subst (EcFol.form_of_expr mhr cond) in
      let branch =
        match EcFol.sform_of_form cond with
        | SFtrue  -> strue
        | SFfalse -> sfalse
        | _ -> raise NotAValue in

      for_stmt subst branch

    | Swhile (cond, body) -> begin
      let cond = eval subst (EcFol.form_of_expr mhr cond) in

      match EcFol.sform_of_form cond with
      | SFtrue ->
        let subst = for_stmt subst body in
        let subst = for_instr subst instr in
        subst

      | SFfalse ->
        subst

      | _ ->
        raise NotAValue
      end

    | Sabstract _
    | Sassert   _
    | Smatch    _
    | Srnd      _ -> raise NotAValue

    and for_stmt (subst : EcPV.PVM.subst) (stmt : stmt) =
    List.fold_left for_instr subst stmt.s_node

  in

  fun ((fpath, args) : xpath * expr list) ->
    try
      let aout =
        doit fpath (List.map (cbv -| EcFol.form_of_expr mhr) args)
      in Option.map (EcFol.expr_of_form mhr) aout
    with NotAValue -> None
