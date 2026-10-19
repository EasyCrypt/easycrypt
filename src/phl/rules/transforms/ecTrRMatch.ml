(* -------------------------------------------------------------------- *)
open EcModules
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the [rmatch] transformation, resolved: the position of
   the match and its constructor are integer indices. *)
type tr_rmatch = {
  trrm_at   : EcMatching.Position.nm_codepos1;
  trrm_ctor : int;
}

type EcPlTransform.transform += TrRMatch of tr_rmatch

(* -------------------------------------------------------------------- *)
(* Decide the match at index [k] in favour of its [j]-th constructor, its
   arguments being assigned to fresh program variables; the prefix must
   establish that constructor. *)
let rmatch (p : tr_rmatch) (ctxt : tr_ctxt) (s : stmt) =
  let r =
    EcPlRCond.rmatch_select
      ctxt.trc_env ctxt.trc_me p.trrm_at p.trrm_ctor s in
  { trr_me  = r.rm_me;
    trr_s   = r.rm_unframed;
    trr_obl = [OPrefixPost { opp_prefix = r.rm_hd; opp_cond = r.rm_post; }]; }

let () =
  register (function
    | TrRMatch p -> Some (rmatch p)
    | _ -> None)
