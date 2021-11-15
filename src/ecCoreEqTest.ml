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

  | Tglob mp, _ when EcEnv.NormMp.tglob_reducible env mp ->
      for_type env (EcEnv.NormMp.norm_tglob env mp) t2

  | _, Tglob mp when EcEnv.NormMp.tglob_reducible env mp ->
      for_type env t1 (EcEnv.NormMp.norm_tglob env mp)

  | Tconstr (p1, lt1), Tconstr (p2, lt2) when EcPath.p_equal p1 p2 ->
      if
           List.length lt1 = List.length lt2
        && List.all2 (for_type env) lt1 lt2
      then true
      else
        if   Ty.defined p1 env
        then for_type env (Ty.unfold p1 lt1 env) (Ty.unfold p2 lt2 env)
        else false

  | Tconstr(p1,lt1), _ when Ty.defined p1 env ->
      for_type env (Ty.unfold p1 lt1 env) t2

  | _, Tconstr(p2,lt2) when Ty.defined p2 env ->
      for_type env t1 (Ty.unfold p2 lt2 env)

  | _, _ -> false
