(* -------------------------------------------------------------------- *)
open EcModules
open EcPlTransform

(* -------------------------------------------------------------------- *)
(* Parameters of the [rndsem] transformation, resolved: the start of the
   suffix is an integer index. *)
type tr_rndsem = {
  trrs_at     : EcMatching.Position.nm_codegap1;
  trrs_reduce : bool;
}

type EcPlTransform.transform += TrRndSem of tr_rndsem

(* -------------------------------------------------------------------- *)
(* Replace the suffix [c[k..)] by its semantic sampling. The variables read
   by the postcondition are only needed (and computed) when reducing. *)
let rndsem (p : tr_rndsem) (ctxt : tr_ctxt) (s : stmt) =
  let s1, s2 = EcMatching.Position.split_at_nmcgap1 p.trrs_at s in
  let used = if p.trrs_reduce then Some (Lazy.force ctxt.trc_post) else None in
  let me, s2 =
    try  EcPlRndSem.semrnd ctxt.trc_env ctxt.trc_me used s2
    with EcPlRndSem.InvalidSemRnd -> raise (InvalidTransform "semrnd") in
  { trr_me = me; trr_s = stmt (s1 @ s2); trr_obl = []; }

let () =
  register (function
    | TrRndSem p -> Some (rndsem p)
    | _ -> None)
