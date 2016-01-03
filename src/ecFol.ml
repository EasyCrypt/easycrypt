(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 * 
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcIdent
open EcUtils
open EcTypes
open EcModules
open EcMemory
open EcBigInt.Notations

module BI = EcBigInt
module CI = EcCoreLib

(* -------------------------------------------------------------------- *)
include EcCoreFol

(* -------------------------------------------------------------------- *)
let f_eqparams f1 ty1 vs1 m1 f2 ty2 vs2 m2 =
  let f_pvlocs f ty vs m =
    let arg = f_pvarg f ty m in
    if List.length vs = 1 then [arg]
    else
      let t = Array.of_list vs in
      let t = Array.mapi (fun i vd -> f_proj arg i vd.v_type) t in
      Array.to_list t
  in

  match vs1, vs2 with
  | Some vs1, Some vs2 ->
      if   List.length vs1 = List.length vs2
      then f_eqs (f_pvlocs f1 ty1 vs1 m1) (f_pvlocs f2 ty2 vs2 m2)
      else f_eq  (f_tuple (f_pvlocs f1 ty1 vs1 m1))
                 (f_tuple (f_pvlocs f2 ty2 vs2 m2))

  | Some vs1, None ->
      f_eq (f_tuple (f_pvlocs f1 ty1 vs1 m1)) (f_pvarg f2 ty2 m2)

  | None, Some vs2 ->
      f_eq (f_pvarg f1 ty1 m1) (f_tuple (f_pvlocs f2 ty2 vs2 m2))

  | None, None ->
      f_eq (f_pvarg f1 ty1 m1) (f_pvarg f2 ty2 m2)

let f_eqres f1 ty1 m1 f2 ty2 m2 =
  f_eq (f_pvar (pv_res f1) ty1 m1) (f_pvar (pv_res f2) ty2 m2)

let f_eqglob mp1 m1 mp2 m2 =
  f_eq (f_glob mp1 m1) (f_glob mp2 m2)

(* -------------------------------------------------------------------- *)
let f_op_real_of_int = (* CORELIB *)
  f_op CI.CI_Real.p_real_of_int [] (tfun tint treal)

let f_real_of_int f  = f_app f_op_real_of_int [f] treal
let f_rint n         = f_real_of_int (f_int n)

let f_r0 = f_rint BI.zero
let f_r1 = f_rint BI.one

let destr_rint f =
  match f.f_node with
  | Fapp (op, [f1]) when f_equal f_op_real_of_int op -> begin
      try destr_int f1 with DestrError _ -> destr_error "destr_rint"
  end

  | _ -> destr_error "destr_rint"

(* -------------------------------------------------------------------- *)
let fop_int_le     = f_op CI.CI_Int .p_int_le    [] (toarrow [tint ; tint ] tbool)
let fop_int_lt     = f_op CI.CI_Int .p_int_lt    [] (toarrow [tint ; tint ] tbool)
let fop_real_le    = f_op CI.CI_Real.p_real_le   [] (toarrow [treal; treal] tbool)
let fop_real_lt    = f_op CI.CI_Real.p_real_lt   [] (toarrow [treal; treal] tbool)
let fop_real_add   = f_op CI.CI_Real.p_real_add  [] (toarrow [treal; treal] treal)
let fop_real_opp   = f_op CI.CI_Real.p_real_opp  [] (toarrow [treal] treal)
let fop_real_mul   = f_op CI.CI_Real.p_real_mul  [] (toarrow [treal; treal] treal)
let fop_real_div   = f_op CI.CI_Real.p_real_div  [] (toarrow [treal; treal] treal)
let fop_real_abs   = f_op CI.CI_Real.p_real_abs  [] (toarrow [treal]        treal) 


let f_int_le f1 f2 = f_app fop_int_le [f1; f2] tbool
let f_int_lt f1 f2 = f_app fop_int_lt [f1; f2] tbool

(* -------------------------------------------------------------------- *)
let f_real_le  f1 f2 = f_app fop_real_le  [f1; f2] tbool
let f_real_lt  f1 f2 = f_app fop_real_lt  [f1; f2] tbool
let f_real_add f1 f2 = f_app fop_real_add [f1; f2] treal
let f_real_opp f     = f_app fop_real_opp [f]      treal
let f_real_mul f1 f2 = f_app fop_real_mul [f1; f2] treal
let f_real_div f1 f2 = f_app fop_real_div [f1; f2] treal
let f_real_abs f     = f_app fop_real_abs [f]      treal

let f_real_sub f1 f2 =
  f_real_add f1 (f_real_opp f2)

(* -------------------------------------------------------------------- *)
let fop_in_supp ty = f_op CI.CI_Distr.p_in_supp [ty] (toarrow [ty; tdistr ty] tbool)
let fop_mu_x    ty = f_op CI.CI_Distr.p_mu_x    [ty] (toarrow [tdistr ty; ty] treal)
let fop_mu      ty = f_op CI.CI_Distr.p_mu      [ty] (toarrow [tdistr ty; tcpred ty] treal)

let f_in_supp f1 f2 = f_app (fop_in_supp f1.f_ty) [f1; f2] tbool
let f_mu_x    f1 f2 = f_app (fop_mu_x f2.f_ty) [f1; f2] treal

let proj_distr_ty env ty = 
   match (EcEnv.Ty.hnorm ty env).ty_node with
  | Tconstr(_,lty) when List.length lty = 1  -> 
    List.hd lty
  | _ -> assert false 

let f_mu env f1 f2 =
  f_app (fop_mu (proj_distr_ty env f1.f_ty)) [f1; f2] treal

let fop_weight ty = (* CORELIB *)
  f_op CI.CI_Distr.p_weight [ty] (tfun (tdistr ty) treal)

let f_weight ty d =
  f_app (fop_weight ty) [d] treal

(* -------------------------------------------------------------------- *)
let f_losslessF f = f_bdHoareF f_true f f_true FHeq f_r1

(* -------------------------------------------------------------------- *)
let f_identity ?(name = "x") ty =
  let name  = EcIdent.create name in
    f_lambda [name, GTty ty] (f_local name ty)

(* -------------------------------------------------------------------- *)
let f_int_opp_simpl f =
  match f.f_node with
  | Fapp (op, [f]) when f_equal op fop_int_opp -> f
  | _ -> if f_equal f_i0 f then f_i0 else f_int_opp f

let f_int_add_simpl f1 f2 =
  try  f_int (destr_int f1 +^ destr_int f2)
  with DestrError _ ->
         if f_equal f_i0 f1 then f2
    else if f_equal f_i0 f2 then f1
    else match f2.f_node with
    | Fapp (op, [f2])
         when f_equal op fop_int_opp && f_equal f1 f2
      -> f_i0
    | _ -> f_int_add f1 f2

let f_int_sub_simpl f1 f2 =
  f_int_add_simpl f1 (f_int_opp_simpl f2)

let f_int_mul_simpl f1 f2 =
  try  f_int (destr_int f1 *^ destr_int f2)
  with DestrError _ ->
         if f_equal f_i0 f1 || f_equal f_i0 f2 then f_i0
    else if f_equal f_i1 f1 then f2
    else if f_equal f_i1 f2 then f1
    else f_int_mul f1 f2

(* -------------------------------------------------------------------- *)
let destr_rdivint f =
  match f.f_node with
  | Fapp (op, [f1; f2]) when f_equal op fop_real_div -> begin
      try  (destr_rint f1, destr_rint f2)
      with DestrError _ -> destr_error "rdivint"
  end
  | _ -> destr_error "rdivint"

let norm_real_int_div n1 n2 =
  if BI.sign n2 = 0 then f_real_div (f_rint n1) (f_rint n2) else
  if BI.sign n1 = 0 then f_r0 else

  let n1, n2 =
    match BI.gcd n1 n2 with
    | n when BI.equal n BI.one -> (n1, n2)
    | n -> (n1/^n, n2/^n)
  in
       if BI.equal n1 BI.zero then f_r0
  else if BI.equal n2 BI.one  then f_rint n1
  else if BI.sign  n2 < 0     then f_real_div (f_rint (~^n1)) (f_rint (~^n2))
  else f_real_div (f_rint n1) (f_rint n2)

let f_real_add_simpl f1 f2 =
  try  f_rint (destr_rint f1 +^ destr_rint f2)
  with DestrError _ ->
    try
      let (n1, d1), (n2, d2) = destr_rdivint f1, destr_rdivint f2 in
      if   BI.sign d1 = 0 || BI.sign d2 = 0
      then norm_real_int_div (n1 *^ n2) BI.zero
      else norm_real_int_div (n1*^d2 +^ n2*^d1) (d1*^d2)
    with DestrError _ ->
           if f_equal f_r0 f1 then f2
      else if f_equal f_r0 f2 then f1
      else match f2.f_node with
      | Fapp (op, [f2])
           when f_equal op fop_real_opp && f_equal f1 f2
        -> f_r0
      | _ -> f_real_add f1 f2

let f_real_opp_simpl f =
  match f.f_node with
  | Fapp (op, [f]) when f_equal op fop_real_opp -> f
  | _ -> if f_equal f_r0 f then f_r0 else f_real_opp f

let f_real_sub_simpl f1 f2 =
  f_real_add_simpl f1 (f_real_opp_simpl f2)

let rec f_real_mul_simpl f1 f2 =
  match f1.f_node, f2.f_node with
  | Fapp (op1, [f1_1; f1_2]), Fapp (op2, [f2_1; f2_2])
      when f_equal op1 fop_real_div
        && f_equal op2 fop_real_div
    -> f_real_div_simpl
         (f_real_mul_simpl f1_1 f2_1)
         (f_real_mul_simpl f1_2 f2_2)

  | _, Fapp (op2, [f2_1; f2_2]) when f_equal op2 fop_real_div ->
      f_real_div_simpl (f_real_mul_simpl f1 f2_1) f2_2

  | Fapp (op1, [f1_1; f1_2]), _ when f_equal op1 fop_real_div ->
      f_real_div_simpl (f_real_mul_simpl f1_1 f2) f1_2

  | _ ->
      try  f_rint (destr_rint f1 *^ destr_rint f2)
      with DestrError _ ->
             if f_equal f_r0 f1 || f_equal f_r0 f2 then f_r0
        else if f_equal f_r1 f1 then f2
        else if f_equal f_r1 f2 then f1
        else f_real_mul f1 f2

and f_real_div_simpl f1 f2 =
  match f1.f_node, f2.f_node with
  | Fapp (op1, [f1_1; f1_2]), Fapp (op2, [f2_1; f2_2])
      when f_equal op1 fop_real_div
        && f_equal op2 fop_real_div
    -> f_real_div_simpl
         (f_real_mul_simpl f1_1 f2_2)
         (f_real_mul_simpl f1_2 f2_1)

  | _, Fapp (op2, [f2_1; f2_2]) when f_equal op2 fop_real_div ->
      f_real_div_simpl (f_real_mul_simpl f1 f2_2) f2_1

  | Fapp (op, [f1_1; f1_2]), _ when f_equal op fop_real_div ->
      f_real_div_simpl f1_1 (f_real_mul_simpl f1_2 f2)

  | _ ->
      try  norm_real_int_div (destr_rint f1) (destr_rint f2)
      with DestrError _ ->
        if f_equal f2 f_r1 then f1 else f_real_div f1 f2

(* -------------------------------------------------------------------- *)
let rec f_let_simpl lp f1 f2 =
  match lp with
  | LSymbol (id, _) -> begin
      match Mid.find_opt id (f_fv f2) with
      | None   -> f2
      | Some i ->
          if   i = 1 || can_subst f1
          then Fsubst.f_subst_local id f1 f2
          else f_let lp f1 f2
    end

  | LTuple ids -> begin
      match f1.f_node with
      | Ftuple fs ->
          let (d, s) =
            List.fold_left2 (fun (d, s) (id, ty) f1 ->
              match Mid.find_opt id (f_fv f2) with
              | None   -> (d, s)
              | Some i ->
                  if   i = 1 || can_subst f1
                  then (d, Mid.add id f1 s)
                  else (((id, ty), f1) :: d, s))
              ([], Mid.empty) ids fs
          in
            List.fold_left
              (fun f2 (id, f1) -> f_let (LSymbol id) f1 f2)
              (Fsubst.subst_locals s f2) d
      | _ ->
        let x = EcIdent.create "tpl" in
        let ty = ttuple (List.map snd ids) in
        let lpx = LSymbol(x,ty) in
        let fx = f_local x ty in
        let tu = f_tuple (List.mapi (fun i (_,ty') -> f_proj fx i ty') ids) in
        f_let_simpl lpx f1 (f_let_simpl lp tu f2)
    end

  | LRecord (_, ids) ->
      let check (id, _) =
        id |> omap (fun id -> not (Mid.mem id (f_fv f2))) |> odfl true
      in if List.for_all check ids then f2 else f_let lp f1 f2

let f_lets_simpl =
  (* FIXME : optimize this *)
  List.fold_right (fun (lp,f1) f2 -> f_let_simpl lp f1 f2)

let rec f_app_simpl f args ty =
  f_betared (f_app f args ty)

and f_betared f =
  let tx fo fp = if f_equal fo fp || can_betared fo then fp else f_betared fp in

  match f.f_node with
  | Fapp ({ f_node = Fquant (Llambda, bds, body)}, args) ->
      let (bds1, bds2), (args1, args2) = List.prefix2 bds args in
      let bind  = fun subst (x, _) arg -> Fsubst.f_bind_local subst x arg in
      let subst = Fsubst.f_subst_id in
      let subst = List.fold_left2 bind subst bds1 args1 in
      f_app (f_quant Llambda bds2 (Fsubst.f_subst ~tx subst body)) args2 f.f_ty
  | _ -> f

and can_betared f =
  match f.f_node with
  | Fapp ({ f_node = Fquant (Llambda, _, _)}, _) -> true
  | _ -> false

let f_forall_simpl b f =
  let b = List.filter (fun (id,_) -> Mid.mem id (f_fv f)) b in
  f_forall b f

let f_exists_simpl b f =
  let b = List.filter (fun (id,_) -> Mid.mem id (f_fv f)) b in
  f_exists b f

let f_quant_simpl q b f =
  if q = Lforall then f_forall_simpl b f else f_exists b f

let f_not_simpl f =
  if is_not f then destr_not f
  else if is_true f then f_false
  else if is_false f then f_true
  else f_not f

let f_and_simpl f1 f2 =
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false
  else f_and f1 f2

let f_ands_simpl = List.fold_right f_and_simpl

let f_anda_simpl f1 f2 =
  if is_true f1 then f2
  else if is_false f1 then f_false
  else if is_true f2 then f1
  else if is_false f2 then f_false
  else f_anda f1 f2

let f_andas_simpl = List.fold_right f_anda_simpl

let f_or_simpl f1 f2 =
  if is_true f1 then f_true
  else if is_false f1 then f2
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_or f1 f2

let f_ora_simpl f1 f2 =
  if is_true f1 then f_true
  else if is_false f1 then f2
  else if is_true f2 then f_true
  else if is_false f2 then f1
  else f_ora f1 f2

let f_imp_simpl f1 f2 =
  if is_true f1 then f2
  else if is_false f1 || is_true f2 then f_true
  else if is_false f2 then f_not_simpl f1
  else
    if f_equal f1 f2 then f_true
    else f_imp f1 f2
    (* FIXME : simplify x = f1 => f2 into x = f1 => f2{x<-f2} *)

let bool_val f =
  if is_true f then Some true
  else if is_false f then Some false
  else None

let f_proj_simpl f i ty =
  match f.f_node with
  | Ftuple args -> List.nth args i
  | _ -> f_proj f i ty

let f_if_simpl f1 f2 f3 =
  if f_equal f2 f3 then f2
  else match bool_val f1, bool_val f2, bool_val f3 with
  | Some true, _, _  -> f2
  | Some false, _, _ -> f3
  | _, Some true, _  -> f_imp_simpl (f_not_simpl f1) f3
  | _, Some false, _ -> f_anda_simpl (f_not_simpl f1) f3
  | _, _, Some true  -> f_imp_simpl f1 f2
  | _, _, Some false -> f_anda_simpl f1 f2
  | _, _, _          -> f_if f1 f2 f3

let f_imps_simpl = List.fold_right f_imp_simpl

let rec f_iff_simpl f1 f2 =
       if f_equal  f1 f2 then f_true
  else if is_true  f1    then f2
  else if is_false f1    then f_not_simpl f2
  else if is_true  f2    then f1
  else if is_false f2    then f_not_simpl f1
  else
    match f1.f_node, f2.f_node with
    | Fapp ({f_node = Fop (op1, [])}, [f1]),
      Fapp ({f_node = Fop (op2, [])}, [f2]) when
        (EcPath.p_equal op1 CI.CI_Bool.p_not &&
         EcPath.p_equal op2 CI.CI_Bool.p_not)
        -> f_iff_simpl f1 f2
    | _ -> f_iff f1 f2

let rec f_eq_simpl f1 f2 =
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fint _ , Fint _ -> f_false

  | Fapp (op1, [{f_node = Fint _}]), Fapp (op2, [{f_node = Fint _}])
      when f_equal op1 f_op_real_of_int &&
           f_equal op2 f_op_real_of_int
    -> f_false

  | Fop (op1, []), Fop (op2, []) when
         (EcPath.p_equal op1 CI.CI_Bool.p_true  &&
          EcPath.p_equal op2 CI.CI_Bool.p_false  )
      || (EcPath.p_equal op2 CI.CI_Bool.p_true  &&
          EcPath.p_equal op1 CI.CI_Bool.p_false  )
    -> f_false

  | Ftuple fs1, Ftuple fs2 when List.length fs1 = List.length fs2 ->
      f_andas_simpl (List.map2 f_eq_simpl fs1 fs2) f_true

  | _ -> f_eq f1 f2

let f_int_le_simpl f1 f2 =
  if f_equal f1 f2 then f_true
  else match f1.f_node, f2.f_node with
  | Fint x1, Fint x2 -> f_bool (BI.compare x1 x2 <= 0)
  | _, _ -> f_int_le f1 f2

let f_int_lt_simpl f1 f2 =
  if f_equal f1 f2 then f_false
  else match f1.f_node, f2.f_node with
  | Fint x1 , Fint x2 -> f_bool (BI.compare x1 x2 < 0)
  | _, _ -> f_int_lt f1 f2

let f_real_le_simpl f1 f2 =
  if f_equal f1 f2 then f_true else
    match f1.f_node, f2.f_node with
    | Fapp (op1, [{f_node = Fint x1}]), Fapp (op2, [{f_node = Fint x2}])
        when f_equal op1 f_op_real_of_int
          && f_equal op2 f_op_real_of_int
        -> f_bool (BI.compare x1 x2 <= 0)

    | _, _ -> f_real_le f1 f2

let f_real_lt_simpl f1 f2 =
  if f_equal f1 f2 then f_false else
    match f1.f_node, f2.f_node with
    | Fapp (op1, [{f_node = Fint x1}]), Fapp (op2, [{f_node = Fint x2}])
        when f_equal op1 f_op_real_of_int
          && f_equal op2 f_op_real_of_int
        -> f_bool (BI.compare x1 x2 < 0)

    | _, _ -> f_real_lt f1 f2

(* -------------------------------------------------------------------- *)
type op_kind = [
  | `True
  | `False
  | `Not
  | `And   of [`Asym | `Sym]
  | `Or    of [`Asym | `Sym]
  | `Imp
  | `Iff
  | `Eq
  | `Int_le
  | `Int_lt
  | `Real_le
  | `Real_lt
  | `Int_add
  | `Int_mul
  | `Int_pow
  | `Int_opp
  | `Real_add
  | `Real_opp
  | `Real_mul
  | `Real_div
]

let operators =
  let operators =
    [CI.CI_Bool.p_true    , `True     ;
     CI.CI_Bool.p_false   , `False    ;
     CI.CI_Bool.p_not     , `Not      ;
     CI.CI_Bool.p_anda    , `And `Asym;
     CI.CI_Bool.p_and     , `And `Sym ;
     CI.CI_Bool.p_ora     , `Or  `Asym;
     CI.CI_Bool.p_or      , `Or  `Sym ;
     CI.CI_Bool.p_imp     , `Imp      ;
     CI.CI_Bool.p_iff     , `Iff      ;
     CI.CI_Bool.p_eq      , `Eq       ;
     CI.CI_Int .p_int_le  , `Int_le   ;
     CI.CI_Int .p_int_lt  , `Int_lt   ;
     CI.CI_Int .p_int_add , `Int_add  ;
     CI.CI_Int .p_int_opp , `Int_opp  ;
     CI.CI_Int .p_int_mul , `Int_mul  ;
     CI.CI_Int .p_int_pow , `Int_pow  ;
     CI.CI_Real.p_real_add, `Real_add ;
     CI.CI_Real.p_real_opp, `Real_opp ;
     CI.CI_Real.p_real_mul, `Real_mul ;
     CI.CI_Real.p_real_div, `Real_div ;
     CI.CI_Real.p_real_le , `Real_le  ;
     CI.CI_Real.p_real_lt , `Real_lt  ; ]
  in

  let tbl = EcPath.Hp.create 11 in
    List.iter (fun (p, k) -> EcPath.Hp.add tbl p k) operators;
    tbl

(* -------------------------------------------------------------------- *)
let op_kind (p : EcPath.path) : op_kind option =
  EcPath.Hp.find_opt operators p

(* -------------------------------------------------------------------- *)
let is_logical_op op =
  match op_kind op with
  | Some (
        `Not | `And _ | `Or _ | `Imp | `Iff | `Eq
      | `Int_le   | `Int_lt   | `Real_le  | `Real_lt
      | `Int_add  | `Int_opp  | `Int_mul
      | `Real_add | `Real_opp | `Real_mul | `Real_div
   ) -> true

  | _ -> false

(* -------------------------------------------------------------------- *)
type sform =
  | SFint   of BI.zint
  | SFlocal of EcIdent.t
  | SFpvar  of EcTypes.prog_var * memory
  | SFglob  of EcPath.mpath * memory

  | SFif    of form * form * form
  | SFmatch of form * form list * ty
  | SFlet   of lpattern * form * form
  | SFtuple of form list
  | SFproj  of form * int
  | SFquant of quantif * (EcIdent.t * gty) * form Lazy.t
  | SFtrue
  | SFfalse
  | SFnot   of form
  | SFand   of [`Asym | `Sym] * (form * form)
  | SFor    of [`Asym | `Sym] * (form * form)
  | SFimp   of form * form
  | SFiff   of form * form
  | SFeq    of form * form
  | SFop    of (EcPath.path * ty list) * (form list)

  | SFhoareF   of hoareF
  | SFhoareS   of hoareS
  | SFbdHoareF of bdHoareF
  | SFbdHoareS of bdHoareS
  | SFequivF   of equivF
  | SFequivS   of equivS
  | SFpr       of pr

  | SFother of form

let sform_of_op (op, ty) args =
  match op_kind op, args with
  | Some (`True ), []       -> SFtrue
  | Some (`False), []       -> SFfalse
  | Some (`Not  ), [f]      -> SFnot f
  | Some (`And b), [f1; f2] -> SFand (b, (f1, f2))
  | Some (`Or  b), [f1; f2] -> SFor  (b, (f1, f2))
  | Some (`Imp  ), [f1; f2] -> SFimp (f1, f2)
  | Some (`Iff  ), [f1; f2] -> SFiff (f1, f2)
  | Some (`Eq   ), [f1; f2] -> SFeq  (f1, f2)

  | _ -> SFop ((op, ty), args)

let rec sform_of_form fp =
  match fp.f_node with
  | Fint   i      -> SFint   i
  | Flocal x      -> SFlocal x
  | Fpvar (x, me) -> SFpvar  (x, me)
  | Fglob (m, me) -> SFglob  (m, me)

  | Fif    (c, f1, f2)  -> SFif    (c, f1, f2)
  | Fmatch (b, fs, ty)  -> SFmatch (b, fs, ty)
  | Flet   (lv, f1, f2) -> SFlet   (lv, f1, f2)
  | Ftuple fs           -> SFtuple fs
  | Fproj (f, i)        -> SFproj  (f,i)

  | Fquant (_, [ ]  , f) -> sform_of_form f
  | Fquant (q, [b]  , f) -> SFquant (q, b, lazy f)
  | Fquant (q, b::bs, f) -> SFquant (q, b, lazy (f_quant q bs f))

  | FhoareF   hf -> SFhoareF   hf
  | FhoareS   hs -> SFhoareS   hs
  | FbdHoareF hf -> SFbdHoareF hf
  | FbdHoareS hs -> SFbdHoareS hs
  | FequivF   ef -> SFequivF   ef
  | FequivS   es -> SFequivS   es
  | Fpr       pr -> SFpr       pr

  | Fop (op, ty) ->
      sform_of_op (op, ty) []

  | Fapp ({ f_node = Fop (op, ty) }, args) ->
      sform_of_op (op, ty) args

  | _ -> SFother fp

(* destr_exists_prenex destructs recursively existentials in a formula
 *  whenever possible.
 * For instance:
 * - E x p1 /\ E y p2 -> [x,y] (p1 /\ p2)
 * - E x p1 /\ E x p2 -> [] (E x p1 /\ E x p2)
 * - p1 => E x p2 -> [x] (p1 => p2)
 * - E x p1 => p2 -> [] (E x p1 => p2)
 *)
let destr_exists_prenex f =
  let disjoint bds1 bds2 =
    List.for_all
      (fun (id1, _) -> List.for_all (fun (id2, _) -> id1 <> id2) bds2)
      bds1
  in

  let rec prenex_exists bds p =
    match sform_of_form p with
    | SFand (`Sym, (f1, f2)) ->
        let (bds1, f1) = prenex_exists [] f1 in
        let (bds2, f2) = prenex_exists [] f2 in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_and f1 f2)
          else (bds, p)

    | SFor (`Sym, (f1, f2)) ->
        let (bds1, f1) = prenex_exists [] f1 in
        let (bds2, f2) = prenex_exists [] f2 in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_or f1 f2)
          else (bds, p)

    | SFimp (f1, f2) ->
        let (bds2, f2) = prenex_exists bds f2 in
          (bds2@bds, f_imp f1 f2)

    | SFquant (Lexists, bd, lazy p) ->
        let (bds, p) = prenex_exists bds p in
          (bd::bds, p)

    | SFif (f, ft, fe) ->
        let (bds1, f1) = prenex_exists [] ft in
        let (bds2, f2) = prenex_exists [] fe in
          if   disjoint bds1 bds2
          then (bds1@bds2@bds, f_if f f1 f2)
          else (bds, p)

    | _ -> (bds, p)
  in
    (* Make it fail as with destr_exists *)
    match prenex_exists [] f with
    | [] , _ -> destr_error "exists"
    | bds, f -> (bds, f)

(* -------------------------------------------------------------------- *)
module type DestrRing = sig
  val le  : form -> form * form
  val lt  : form -> form * form
  val add : form -> form * form
  val opp : form -> form
  val sub : form -> form * form
  val mul : form -> form * form
end

(* -------------------------------------------------------------------- *)
module DestrInt : DestrRing = struct
  let le  = destr_app2_eq ~name:"int_le"  CI.CI_Int.p_int_le
  let lt  = destr_app2_eq ~name:"int_lt"  CI.CI_Int.p_int_lt
  let add = destr_app2_eq ~name:"int_add" CI.CI_Int.p_int_add
  let opp = destr_app1_eq ~name:"int_opp" CI.CI_Int.p_int_opp
  let mul = destr_app2_eq ~name:"int_mul" CI.CI_Int.p_int_mul

  let sub f =
    try  snd_map opp (add f)
    with DestrError _ -> raise (DestrError "int_sub")
    
end

(* -------------------------------------------------------------------- *)
module type DestrReal = sig
  include DestrRing

  val inv : form -> form
  val div : form -> form * form
  val abs : form -> form
end

module DestrReal : DestrReal = struct
  let le  = destr_app2_eq ~name:"real_le"  CI.CI_Real.p_real_le
  let lt  = destr_app2_eq ~name:"real_lt"  CI.CI_Real.p_real_lt
  let add = destr_app2_eq ~name:"real_add" CI.CI_Real.p_real_add
  let opp = destr_app1_eq ~name:"real_opp" CI.CI_Real.p_real_opp
  let mul = destr_app2_eq ~name:"real_mul" CI.CI_Real.p_real_mul
  let inv = destr_app1_eq ~name:"real_inv" CI.CI_Real.p_real_inv
  let div = destr_app2_eq ~name:"real_div" CI.CI_Real.p_real_div
  let abs = destr_app1_eq ~name:"real_abs" CI.CI_Real.p_real_abs

  let sub f =
    try  snd_map opp (add f)
    with DestrError _ -> raise (DestrError "real_sub")
end
