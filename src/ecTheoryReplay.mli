(* ------------------------------------------------------------------ *)
open EcSymbols
open EcPath
open EcParsetree
open EcTheory
open EcThCloning

(* ------------------------------------------------------------------ *)
type ovoptions = {
  clo_abstract : bool;
}

type 'a ovrenv = {
  ovre_ovrd     : EcThCloning.evclone;
  ovre_rnms     : EcThCloning.renaming list;
  ovre_ntclr    : EcPath.Sp.t;
  ovre_opath    : EcPath.path;
  ovre_npath    : EcPath.path;
  ovre_prefix   : (symbol list) EcUtils.pair;
  ovre_glproof  : (ptactic_core option * evtags option) list;
  ovre_abstract : bool;
  ovre_local    : EcTypes.is_local;
  ovre_hooks    : 'a ovrhooks;
}

and 'a ovrhooks = {
  henv      : 'a -> EcSection.scenv;
  hadd_item : 'a -> import:bool -> EcTheory.theory_item_r -> 'a;
  hthenter  : 'a -> thmode -> symbol -> EcTypes.is_local -> 'a;
  hthexit   : 'a -> import:bool -> [`Full | `ClearOnly | `No] -> 'a;
  herr      : 'b . ?loc:EcLocation.t -> string -> 'b;
}

(* -------------------------------------------------------------------- *)
val replay : 'a ovrhooks
  -> abstract:bool -> local:is_local -> incl:bool
  -> clears:Sp.t -> renames:(renaming list)
  -> opath:path -> npath:path -> evclone
  -> 'a -> symbol * bool * theory_item list
  -> axclone list * 'a
