(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* ------------------------------------------------------------------ *)
open EcSymbols
open EcPath
open EcParsetree
open EcTypes
open EcDecl
open EcModules
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
  ovre_local    : bool;
  ovre_hooks    : 'a ovrhooks;
}

and 'a ovrhooks = {
  henv     : 'a -> EcEnv.env;
  hty      : 'a -> (symbol * tydecl) -> 'a;
  hop      : 'a -> (symbol * operator) -> 'a;
  hmodty   : 'a -> (symbol * module_sig) -> 'a;
  hmod     : 'a -> bool -> module_expr -> 'a;
  hax      : 'a -> bool -> (symbol * axiom) -> 'a;
  hexport  : 'a -> EcPath.path -> 'a;
  hbaserw  : 'a -> symbol -> 'a;
  haddrw   : 'a -> EcPath.path * EcPath.path list -> 'a;
  hauto    : 'a -> bool * int * string option * EcPath.path list -> 'a;
  htycl    : 'a -> symbol * typeclass -> 'a;
  hinst    : 'a -> (ty_params * ty) * tcinstance -> 'a;
  husered  : 'a -> (EcPath.path * EcTheory.rule_option * EcTheory.rule option) list -> 'a;
  hthenter : 'a -> thmode -> symbol -> 'a;
  hthexit  : 'a -> [`Full | `ClearOnly | `No] -> 'a;
  herr     : 'b . ?loc:EcLocation.t -> string -> 'b;
}

(* -------------------------------------------------------------------- *)
val replay : 'a ovrhooks
  -> abstract:bool -> local:bool -> incl:bool
  -> clears:Sp.t -> renames:(renaming list)
  -> opath:path -> npath:path -> evclone
  -> 'a -> symbol * ctheory_item list
  ->  axclone list * 'a
