(* -------------------------------------------------------------------- *)
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the [rcond] transformation, resolved: the position of the
   conditional is an integer index. *)
type tr_rcond = {
  trrc_at     : EcMatching.Position.nm_codepos1;
  trrc_branch : bool;
}

type EcPlTransform.transform += TrRCond of tr_rcond

(* -------------------------------------------------------------------- *)
(* Decide the conditional at index [k] in favour of the branch [b]; the
   prefix must establish the corresponding guard. *)
let rcond (p : tr_rcond) (ctxt : tr_ctxt) (s : EcModules.stmt) =
  let hd, g, s =
    EcPlRCond.rcond_select
      (EcMemory.memory ctxt.trc_me) p.trrc_at p.trrc_branch s in
  { trr_me  = ctxt.trc_me;
    trr_s   = s;
    trr_obl = [OPrefixPost { opp_prefix = hd; opp_cond = g; }]; }

let () =
  register (function
    | TrRCond p -> Some (rcond p)
    | _ -> None)
