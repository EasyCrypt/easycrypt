(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)


(* -------------------------------------------------------------------- *)
(* Function for cost                                                    *)
open EcUtils
open EcTypes
open EcFol
open EcEnv

let f_subcond f1 f2 =
  f_or (f_is_inf f1) (f_is_int f2)

let f_xsub f1 f2 =
  f_subcond f1 f2, f_xadd f1 (f_xopp f2)

let cost_sub_self c a =
  let cond, c_self = f_xsub c.c_self a in
  cond, cost_r c_self c.c_calls

let cost_add_self c a =
  let c_self = f_xadd c.c_self a in
  cost_r c_self c.c_calls

(* Add an entry for a oracle to [c.c_calls], if necessary. *)
let cost_add_oracle env c f =
  if EcPath.Mx.mem f c.c_calls
  then c
  else begin
    let m = f.EcPath.x_top in
    assert ( m.m_args = [] &&
             match m.EcPath.m_top with `Local _ -> true | _ -> false);

    let restr = EcEnv.NormMp.get_restr env m in
    let oi = EcSymbols.Msym.find f.EcPath.x_sub restr.mr_oinfos in

    let self = match EcCoreModules.PreOI.cost_self oi with
      | `Unbounded -> assert false
      | `Bounded self -> self in

    let cb = call_bound_r self f_i0 in

    cost_r c.c_self (EcPath.Mx.add f cb c.c_calls)
  end

let cost_sub_call env c f a =
  let c = cost_add_oracle env c f in

  let c_calls = EcPath.Mx.change (fun cb ->
      let cb = oget cb in
      call_bound_r cb.cb_cost (f_int_sub_simpl cb.cb_called a)
      |> some
    ) f c.c_calls in

  cost_r c.c_self c_calls

let cost_add_call env c f a =
  let c = cost_add_oracle env c f in

  let c_calls = EcPath.Mx.change (fun cb ->
      let cb = oget cb in
      call_bound_r cb.cb_cost (f_int_add_simpl cb.cb_called a)
      |> some
    ) f c.c_calls in

  cost_r c.c_self c_calls

let cost_op env op c1 c2 =
  (* Ensure that [c1] and [c2] have the same support. *)
  let c2 = List.fold_left (cost_add_oracle env) c2 (EcPath.Mx.keys c1.c_calls)
  and c1 = List.fold_left (cost_add_oracle env) c1 (EcPath.Mx.keys c2.c_calls) in

  EcPath.Mx.union (fun _ cb1 cb2 ->
    assert (f_equal cb1.cb_cost cb2.cb_cost);
    Some (call_bound_r cb1.cb_cost (op cb1.cb_called cb2.cb_called)))
  c1.c_calls c2.c_calls

let cost_add env c1 c2 =
  let c_calls = cost_op env EcFol.f_int_add_simpl c1 c2 in
  cost_r (f_xadd c1.c_self c2.c_self) c_calls

let cost_sub env c1 c2 =
  let c_calls = cost_op env EcFol.f_int_sub_simpl c1 c2 in
  let cond, self = f_xsub c1.c_self c2.c_self in
  cond, cost_r self c_calls

let cost_map f_xmap f_map c =
  EcPath.Mx.fold (fun f cb res ->
      let c_calls =
        EcPath.Mx.add f
          (call_bound_r (cb.cb_cost) (f_map cb.cb_called))
          res.c_calls in
      cost_r res.c_self c_calls
    ) c.c_calls
    (cost_r (f_xmap c.c_self) EcPath.Mx.empty)

let cost_app c args =
  cost_map (fun c -> f_app_simpl c args txint)
           (fun c -> f_app_simpl c args tint) c

let cost_flatten cost =
  EcPath.Mx.fold (fun _ cb cflat ->
      f_xadd cflat (f_xmuli cb.cb_called cb.cb_cost))
    cost.c_calls cost.c_self

let loaded (env : env) =
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_xint.p_Xint env) &&
  is_some (EcEnv.Theory.by_path_opt EcCoreLib.CI_xint.p_choaretac env)

exception LoadChoareFirst

let check_loaded (env : env) =
  if not (loaded env) then raise LoadChoareFirst

let pp_exn fmt exn =
  match exn with
  | LoadChoareFirst -> Format.fprintf fmt "load the `CHoareTactic' theory first"
  | _ -> raise exn

let _ = EcPException.register pp_exn


(*
module ICHOARE : sig
  val loaded : EcEnv.env -> bool
  val choare_sum : cost -> (form * form) -> cost
  val choare_max : form -> form -> form
end = struct
  open EcCoreLib
  open EcEnv
*)

let q_List    = [EcCoreLib.i_top; "List"]

let tlist =
  let tlist = EcPath.fromqsymbol (q_List, "list") in
  fun ty -> EcTypes.tconstr tlist [ty]

let range =
  let rg = EcPath.fromqsymbol (q_List @ ["Range"], "range") in
  let rg = f_op rg [] (toarrow [tint; tint] (tlist tint)) in
  fun m n -> f_app rg [m; n] (tlist tint)

let f_predT = f_op EcCoreLib.CI_Pred.p_predT [tint] (tpred tint)

let f_op_xbig =
  f_op EcCoreLib.CI_xint.p_big [tint]
    (toarrow [tpred tint; tfun tint txint; tlist tint] txint)

let f_op_big =
  let p_big = EcPath.fromqsymbol ([EcCoreLib.i_top;"StdBigop";"Bigint";"BIA"], "big") in

  f_op p_big [tint]
    (toarrow [tpred tint; tfun tint tint; tlist tint] tint)

let f_xbig f m n =
  f_app f_op_xbig [f_predT; f; range m n] txint

let f_big f m n =
  f_app f_op_big [f_predT; f; range m n] tint

let choare_sum cost (m, n) =
  cost_map (fun f -> f_xbig f m n)
           (fun f -> f_big f m n) cost

(* -------------------------------------------------------------------- *)
(*
(* -------------------------------------------------------------------- *)
(* The cost of an expression evaluation in any memory of a given type
   satisfying some pre-condition. *)
val cost_of_expr : form -> EcMemory.memenv -> EcTypes.expr -> form

(* The cost of an expression evaluation in any memory of a given type. *)
val cost_of_expr_any : EcMemory.memenv -> EcTypes.expr -> form

val free_expr : EcTypes.expr -> bool
 *)
let free_expr e = match e.e_node with
  | Elocal _ | Evar _ | Eint _ -> true

  | Eop _
  | Eproj _ | Etuple _ | Eapp _
  | Equant _ | Elet _ | Eif _ | Ematch _ -> false


(* The cost of an expression evaluation in any memory of type [menv]
   satisfying [pre]. *)
let cost_of_expr pre menv e =
  if free_expr e then f_x0 else f_coe pre menv e

(* The cost of an expression evaluation in any memory of type [menv]. *)
let cost_of_expr_any menv e =
  if free_expr e then f_x0 else f_coe f_true menv e
