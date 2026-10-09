(* -------------------------------------------------------------------- *)
open EcSymbols
open EcFol
open EcAst
open EcEnv

open EcCoreGoal
open EcLowPhlGoal

(* -------------------------------------------------------------------- *)
(* Argument of the hoare [extens] rule: the enumerated variable, by name.
   The node records it resolved in the memory of the goal. *)
type hoare_extens_rule = {
  her_var : symbol;
}

type hoare_extens_node = {
  hen_var : variable;
}

type EcCoreGoal.rule += RHoareExtens of hoare_extens_node

(* -------------------------------------------------------------------- *)
exception InvalidExtens of string

let invalid fmt = Format.kasprintf (fun msg -> raise (InvalidExtens msg)) fmt

(* -------------------------------------------------------------------- *)
(* The size and the [of_int] operator of the bitstring bound to [ty]. *)
let bitstring_binding (env : env) (ty : ty) : int * EcPath.path =
  let size =
    match EcEnv.Circuit.lookup_bitstring_size env ty with
    | Some size -> size
    | None ->
      invalid
        "Failed to get size for type %a (is it finite and does it have a \
         binding to a bistring type (arrays unsupported)?)"
        EcPrinting.(pp_type PPEnv.(ofenv env))
        ty
  in
  let tpath =
    match ty.ty_node with
    | Tconstr (p, _) -> p
    | _ -> invalid "Failed to destructure var type"
  in
  let of_int =
    match EcEnv.Circuit.reverse_type env tpath with
    | [] -> invalid "No bindings found for type of var"
    | `Bitstring {ofint} :: _ -> ofint
    | _ -> invalid "Only finite size bitstring supported"
  in
  size, of_int

(* -------------------------------------------------------------------- *)
(* [s] in which the program variables are substituted by [sb] in the
   right-hand sides of its assignments (normalized); [s] contains only
   assignments. *)
let subst_pv_stmt
    (hyps : LDecl.hyps) (mem : memory) (sb : EcPV.PVM.subst) (s : stmt)
=
  let redmode = EcCircuits.circ_red hyps in
  let env = LDecl.toenv hyps in
  stmt
    (List.map
       (fun i ->
         match i.i_node with
         | Sasgn (lv, e) ->
           let f = ss_inv_of_expr mem e in
           let fi = EcPV.PVM.subst env sb f.inv in
           let fi = EcCallbyValue.norm_cbv redmode hyps fi in
           let e = expr_of_ss_inv {f with inv = fi} in
           EcCoreModules.i_asgn (lv, e)
         | _ -> raise CannotTranslate)
       s.s_node)

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side conditions (no
   exceptional postcondition, [x] a variable of the memory whose type is
   bound to a bitstring, not written by the program) are part of it, so
   the checker re-validates them. Raises [InvalidExtens] when they do not hold, [CannotTranslate]
   when the statement is not made of assignments. *)
let hoare_extens_subgoals
    (hyps : LDecl.hyps) (hs : sHoareS) (n : hoare_extens_node)
=
  let env = LDecl.toenv hyps in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    invalid "exceptions not supported";

  let m, mt = hs.hs_m in
  let v = n.hen_var in
  begin match EcMemory.lookup v.v_name mt with
  | Some (v', _, _) when v'.v_name = v.v_name
                      && EcTypes.ty_equal v'.v_type v.v_type -> ()
  | _ ->
    invalid "Failed to find var %s in memory %s" v.v_name (EcIdent.name m)
  end;

  let size, of_int = bitstring_binding env v.v_type in

  (* Each instance replaces [v] by a constant in the program, the
     precondition and the postcondition. The postcondition reads [v] in
     the final memory: this is only sound if the program does not write
     [v]. *)
  if EcPV.PV.mem_pv env (EcTypes.pv_loc v.v_name) (EcPV.s_write env hs.hs_s) then
    invalid "extens: the program writes the variable %s" v.v_name;

  List.init (1 lsl size) (fun i ->
      let subst =
        EcPV.PVM.(
          add env (PVloc v.v_name) m
            (EcTypesafeFol.f_op_app env of_int [f_int BI.(of_int i)])
            empty)
      in
      let s = subst_pv_stmt hyps m subst hs.hs_s in
      let subst = EcPV.PVM.subst env subst in
      let pr = subst (hs_pr hs).inv in
      let po = subst (POE.lower (hs_po hs)).inv in
      f_hoareS mt {inv = pr; m} s (POE.lift {inv = po; m}))

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_hoare_extens (r : hoare_extens_rule) (tc : tcenv1) =
  let hs = tc1_as_hoareS tc in
  if not (POE.is_empty (hs_po hs).hsi_inv) then
    tc_error !!tc "exceptions not supported";

  let m, mt = hs.hs_m in
  let v =
    match EcMemory.lookup r.her_var mt with
    | Some (v, _, _) -> v
    | None ->
      tc_error !!tc "Failed to find var %s in memory %s" r.her_var
        (EcIdent.name m)
  in
  let n = { hen_var = v } in
  let sg =
    try  hoare_extens_subgoals (FApi.tc1_hyps tc) hs n
    with InvalidExtens msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc (RHoareExtens n) sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RHoareExtens n ->
         Some (EcPlRecheck.checker_of "hoare-extens" pf_as_hoareS
                 (fun hyps hs -> hoare_extens_subgoals hyps hs n))
     | _ -> None)
