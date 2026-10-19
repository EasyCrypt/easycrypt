(* -------------------------------------------------------------------- *)
open EcAst
open EcModules
open EcPV
open EcPlTransform

module Zpr = EcMatching.Zipper

(* -------------------------------------------------------------------- *)
(* Parameters of the statement change, resolved: the range is an integer
   gap range of the (possibly nested) block at a normalized path, the
   fresh locals are bound by the entry itself (deterministically), and the
   new statement is typed in the memory they extend. *)
type tr_stmt_change = {
  trsc_range : EcMatching.Position.nm_codegap_range;
  trsc_binds : ovariable list;
  trsc_stmt  : stmt;
}

type EcPlTransform.transform += TrStmtChange of tr_stmt_change

(* -------------------------------------------------------------------- *)
(* Replace the range by the new statement, under a local equivalence
   between the two fragments. *)
let stmt_change (p : tr_stmt_change) (ctxt : tr_ctxt) (s : stmt) =
  let env = ctxt.trc_env in
  let (path, (start, fin)), s' = p.trsc_range, p.trsc_stmt in

  let invalid_cpos () = raise (InvalidTransform "invalid code position") in

  let zpr =
    try  Zpr.zipper_of_nm_cpos (path, start) s
    with EcMatching.Position.InvalidCPos -> invalid_cpos () in
  if not (start <= fin && fin - start <= List.length zpr.z_tail) then
    invalid_cpos ();
  let b, epilog = EcUtils.List.takedrop (fin - start) zpr.z_tail in

  let me, _ = EcMemory.bindall_fresh p.trsc_binds ctxt.trc_me in

  (* The code around the fragment: [zpr] without the fragment. *)
  let around = (zpr.z_head, epilog), zpr.z_path in

  (* Inside a loop, the fragment may run several times. Its later runs
     start after the surrounding code of the loop, but also after the
     previous runs of the fragment itself, and from states where the two
     programs only agree on the observable variables (see [obs] below). *)
  let inloop = Zpr.in_loop zpr.z_path in

  (* Collect the variables that may be modified before (a run of) the
     fragment: by the surrounding context and, inside a loop, by the
     previous runs of the original fragment. The frame of the local
     equivalence (computed by the rule from its precondition) only keeps
     what is independent from them. *)
  let modi =
    let modi = zpr_pv `Write `Before env PV.empty around in
    if inloop then is_write_r env modi b else modi in

  (* The variables read by both fragments, assumed equal by the local
     equivalence. *)
  let reads = PV.inter (is_read env b) (is_read env s'.s_node) in

  (* The observable variables: those read by the code that may run after
     the fragment (for an enclosing loop, its guard and its whole body)
     and by the postcondition. Inside a loop, we add the variables read
     by both fragments, i.e. the ones assumed equal by the local
     equivalence below.
     Soundness: the original and new programs are related by "the states
     agree on [obs]" (they are equal before the first run of the
     fragment). The code after the fragment only reads [obs], so it
     preserves this relation. When reaching the fragment, the relation
     implies the equalities of the precondition of the local
     equivalence (their variables are in [obs] when in a loop), the
     frame holds on the original side as no code run so far writes its
     variables (see [modi]), and the local equivalence then
     re-establishes the relation: the observable variables that are
     written are equal, and the other ones are unchanged. *)
  let obs =
    let obs = zpr_pv `Read `After env PV.empty around in
    let obs = if inloop then PV.union obs reads else obs in
    PV.union obs (Lazy.force ctxt.trc_post) in

  let written =
    let written = is_write_r env PV.empty b in
    let written = is_write_r env written s'.s_node in
    PV.inter written obs in

  { trr_me  = me;
    trr_s   = Zpr.zip { zpr with z_tail = s'.s_node @ epilog };
    trr_obl = [OLocalEquiv { ole_locals = EcTrExprChange.locals_of_path zpr.z_path;
                             ole_orig   = stmt b;
                             ole_new    = s';
                             ole_reads  = reads;
                             ole_writes = written;
                             ole_modi   = modi; }]; }

let () =
  register (function
    | TrStmtChange p -> Some (stmt_change p)
    | _ -> None)
