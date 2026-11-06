(* -------------------------------------------------------------------- *)
open EcAst
open EcTypes
open EcFol
open EcPV

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
let wp_asgn_call ?mc env lv (res : ss_inv) (post : ss_inv) =
  assert (res.m = post.m);
  let m = post.m in
  match lv with
  | None -> post
  | Some lv ->
      let lets = lv_subst m lv res.inv in
      { m; inv = mk_let_of_lv_substs ?mc env ([lets], post.inv) }

(* -------------------------------------------------------------------- *)
let subst_args_call env m e s =
  PVM.add env pv_arg m (ss_inv_of_expr m e).inv s

(* -------------------------------------------------------------------- *)
let single_call (name : string) (s : stmt) =
  match s.s_node with
  | [{ i_node = Scall (lv, f, args) }] -> (lv, f, args)
  | _ -> failwith (name ^ ": the statement is not a single call")

(* -------------------------------------------------------------------- *)
let call_error env tc f1 f2 =
  tc_error_lazy !!tc (fun fmt ->
      let ppe = EcPrinting.PPEnv.ofenv env in
      Format.fprintf fmt
        "call cannot be used with a lemma referring to `%a': \
         the last statement is a call to `%a'"
        (EcPrinting.pp_funname ppe) f1
        (EcPrinting.pp_funname ppe) f2)
