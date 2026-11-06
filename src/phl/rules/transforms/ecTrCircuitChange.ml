(* -------------------------------------------------------------------- *)
open EcAst
open EcModules
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the circuit change, resolved: the position is a
   normalized (possibly nested) code position, the fresh locals are bound
   by the entry itself (deterministically), and the new statement is typed
   in the memory they extend. *)
type tr_circuit_change = {
  trcc_at    : EcMatching.Position.nm_codepos;
  trcc_len   : int;
  trcc_binds : ovariable list;
  trcc_stmt  : stmt;
}

type EcPlTransform.transform += TrCircuitChange of tr_circuit_change

(* -------------------------------------------------------------------- *)
let invalid fmt = Format.kasprintf (fun msg -> raise (InvalidTransform msg)) fmt

(* -------------------------------------------------------------------- *)
(* Replace the fragment by the new statement, provided that the circuit
   checker establishes that they agree on the variables to keep. *)
let circuit_change (p : tr_circuit_change) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in

  let mem =
    List.fold_left
      (fun mem v -> fst (EcMemory.bind_fresh v mem))
      ctxt.trc_me p.trcc_binds in

  let s' = p.trcc_stmt in

  let zp =
    try  Zpr.zipper_of_nm_cpos p.trcc_at s
    with EcMatching.Position.InvalidCPos -> invalid "invalid code position" in

  if not (0 <= p.trcc_len && p.trcc_len <= List.length zp.z_tail) then
    invalid "cannot find %d consecutive instructions at given position"
      p.trcc_len;

  let target, tl = EcUtils.List.takedrop p.trcc_len zp.z_tail in

  (* [keep] is the set of variables on which [target] and [s'] must
     agree. Let [R] be the variables read by both [target] and [s'].
     We take for [keep]:
     - the variables read by the code that may run after the fragment
       (for each enclosing [while], its guard and its whole body),
       and by the postcondition;
     - if the fragment is inside a loop, [R].
     Soundness: the original and the new programs are related by
     "the states agree on [keep]" (they are equal before the first
     run of the fragment). The code that may run after the fragment
     only reads [keep], so preserves this relation. When reaching the
     fragment in states [m1] (original) and [m2] (new), let [m] be
     [m2] updated with the values of [m1] on [read(target) \ R].
     Then [m] agrees with [m1] on [read(target)] and on [keep] (as
     [R] is included in [keep]), and with [m2] on [read(s')] and on
     [keep]. As [target] and [s'] are deterministic, we get
     [target(m1) =keep target(m) =keep s'(m) =keep s'(m2)], the middle
     equality being the one established by the circuit checker.
     Outside a loop, the fragment is run once, from [m1 = m2], and
     [R] does not need to be kept.
     The circuit checker only accepts assignments (no [raise]): the
     fragments always terminate normally, and an exception raised
     afterwards is observed through the exceptional postconditions,
     whose variables are in [trc_post]. *)
  let keep =
    let zpr = ((zp.z_head, tl), zp.z_path) in
    EcPV.zpr_pv `Read `After env EcPV.PV.empty zpr in
  let keep =
    if Zpr.in_loop zp.z_path then
      EcPV.PV.union keep
        (EcPV.PV.inter
           (EcPV.is_read env target)
           (EcPV.is_read env s'.s_node))
    else keep in
  let keep = EcPV.PV.union keep (Lazy.force ctxt.trc_post) in
  (* The variables that are neither read nor written by [target] and
     [s'] are left unchanged by both and need not be compared. This
     drops the global variables, which [target] and [s'] cannot access
     (this is checked by the circuit checker). *)
  let keep =
    let ts = target @ s'.s_node in
    EcPV.PV.inter keep
      (EcPV.PV.union (EcPV.is_read env ts) (EcPV.is_write env ts)) in
  let st = EcLowCircuits.create_state (EcEnv.gstate env) in

  let equiv =
    try EcCircuits.instrs_equiv ctxt.trc_hyps ~keep mem st target s'.s_node
    with e ->
      invalid "circuit-equivalence checker error: %s" (Printexc.to_string e)
  in
  if not equiv then
    invalid "statements are not circuit-equivalent";

  { trr_me  = mem;
    trr_s   = Zpr.zip { zp with z_tail = s'.s_node @ tl };
    trr_obl = []; }

let () =
  register (function
    | TrCircuitChange p -> Some (circuit_change p)
    | _ -> None)
