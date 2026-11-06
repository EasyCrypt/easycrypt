(* -------------------------------------------------------------------- *)
open EcFol
open EcAst
open EcEnv

open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* The [extens] rule on [all p (iota_ s n)] has no parameters: [s] and [n]
   are integer literals read from the goal. *)
type EcCoreGoal.rule += RFolExtens

(* -------------------------------------------------------------------- *)
exception InvalidExtens of string

(* -------------------------------------------------------------------- *)
(* Pure core shared by the rule and its checker. Its side condition (the
   goal is [all p (iota_ s n)], [s] and [n] integer literals) is part of
   it, so the checker re-validates it. Raises [InvalidExtens]
   otherwise. *)
let fol_extens_subgoals (hyps : LDecl.hyps) (f : form) : form list =
  let invalid msg = raise (InvalidExtens msg) in
  match sform_of_form f with
  | SFop ((p, [tp]), [fpred; flist])
      when EcPath.p_equal p EcCoreLib.CI_List.p_all
        && EcTypes.ty_equal tp EcTypes.tint
    -> begin
      match sform_of_form flist with
      | SFop ((p, []), [fstart; flen])
          when EcPath.p_equal p EcCoreLib.CI_List.p_iota ->
        let start =
          match sform_of_form fstart with
          | SFint i -> EcBigInt.to_int i
          | _ -> invalid "Iota start should be constant"
        in

        let len =
          match sform_of_form flen with
          | SFint i -> EcBigInt.to_int i
          | _ -> invalid "Iota length should be constant"
        in

        List.init len (fun i ->
            EcTypesafeFol.f_app hyps fpred
              [f_int EcBigInt.(of_int (i + start))])

      | _ -> invalid "Unsupported List pattern"
    end

  | _ -> invalid "Wrong goal shape"

(* -------------------------------------------------------------------- *)
(* Rule (TCB). *)
let t_fol_extens (tc : tcenv1) =
  let sg =
    try  fol_extens_subgoals (FApi.tc1_hyps tc) (FApi.tc1_goal tc)
    with InvalidExtens msg -> tc_error !!tc "%s" msg in
  FApi.xrule1 tc RFolExtens sg

(* -------------------------------------------------------------------- *)
let () =
  register_rule_checker
    (function
     | RFolExtens ->
         Some (EcPlRecheck.checker_of "fol-extens" (fun _ f -> f)
                 fol_extens_subgoals)
     | _ -> None)
