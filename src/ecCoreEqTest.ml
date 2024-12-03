(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcUtils
open EcTypes
open EcEnv

(* -------------------------------------------------------------------- *)
type 'a eqtest  = env -> 'a -> 'a -> bool

(* -------------------------------------------------------------------- *)
let rec for_type env t1 t2 =
  ty_equal t1 t2 || for_type_r env t1 t2

(* -------------------------------------------------------------------- *)
and for_type_r env t1 t2 =
  match t1.ty_node, t2.ty_node with
  | Tunivar uid1, Tunivar uid2 -> EcUid.uid_equal uid1 uid2

  | Tvar i1, Tvar i2 -> i1 = i2

  | Ttuple lt1, Ttuple lt2 ->
        List.length lt1 = List.length lt2
     && List.all2 (for_type env) lt1 lt2

  | Tfun (t1, t2), Tfun (t1', t2') ->
      for_type env t1 t1' && for_type env t2 t2'

  | Tglob m1, Tglob m2 -> EcIdent.id_equal m1 m2

  | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
      if
           List.length lt1 = List.length lt2
        && List.all2 (for_etyarg env) lt1 lt2
      then true
      else
        if   Ty.defined p1 env
        then for_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env)
        else false

  | Tconstr (p1, lt1), _ when Ty.defined p1 env ->
      for_type env (Ty.unfold p1 lt1 env) t2

  | _, Tconstr (p2, lt2) when Ty.defined p2 env ->
      for_type env t1 (Ty.unfold p2 lt2 env)

  | _, _ -> false

(* -------------------------------------------------------------------- *)
and for_etyarg env ((ty1, tcws1) : etyarg) ((ty2, tcws2) : etyarg) =
  for_type env ty1 ty2 && for_tcws env tcws1 tcws2

and for_etyargs env (tyargs1 : etyarg list) (tyargs2 : etyarg list) =
     List.length tyargs1 = List.length tyargs2
  && List.for_all2 (for_etyarg env) tyargs1 tyargs2

and for_tcw env (tcw1 : tcwitness) (tcw2 : tcwitness) =
  match tcw1, tcw2 with
  | TCIConcrete tcw1, TCIConcrete tcw2 ->
       EcPath.p_equal tcw1.path tcw2.path
    && for_etyargs env tcw1.etyargs tcw2.etyargs

  | TCIAbstract { support = `Var v1; offset = o1 },
    TCIAbstract { support = `Var v2; offset = o2 } ->
    EcIdent.id_equal v1 v2 && o1 = o2

  | TCIAbstract { support = `Univar v1; offset = o1 },
    TCIAbstract { support = `Univar v2; offset = o2 } ->
    EcUid.uid_equal v1 v2 && o1 = o2

  | TCIAbstract { support = `Abs p1; offset = o1 },
    TCIAbstract { support = `Abs p2; offset = o2 } ->
    EcPath.p_equal p1 p2 && o1 = o2

  | _, _ ->
    false
    
and for_tcws env (tcws1 : tcwitness list) (tcws2 : tcwitness list) =
    List.length tcws1 = List.length tcws2
 && List.for_all2 (for_tcw env) tcws1 tcws2
