(* -------------------------------------------------------------------- *)
open EcSymbols
open EcFormat
open EcPath
open EcUidgen
open EcParsetree
open EcTypes
open EcDecl
open EcTypesmod

(* -------------------------------------------------------------------- *)
type 'a pr = 'a -> Pprint.document

val pretty : Pprint.document -> unit

(* -------------------------------------------------------------------- *)
val pr_type     : ?vmap:NameGen.t -> ty pr
val pr_dom      : EcTypes.dom pr
val pr_typedecl : (EcIdent.t * tydecl  ) pr
val pr_opdecl   : (EcIdent.t * operator) pr
val pr_axiom    : (EcIdent.t * axiom   ) pr
val pr_modtype  : (EcIdent.t * tymod   ) pr
val pr_module   : module_expr pr
val pr_export   : EcPath.path pr
val pr_theory   : (EcIdent.t * ctheory) pr

(* -------------------------------------------------------------------- *)
val pp_located : Location.t -> 'a pp -> 'a pp
val pp_of_pr   : 'a pr -> 'a pp

(* -------------------------------------------------------------------- *)
val pp_qsymbol : qsymbol pp
val pp_path    : EcPath.path pp

(* -------------------------------------------------------------------- *)
val pp_type     : ?vmap:NameGen.t -> ty pp
val pp_dom      : EcTypes.dom pp
val pp_typedecl : (EcIdent.t * tydecl  ) pp
val pp_opdecl   : (EcIdent.t * operator) pp
val pp_axiom    : (EcIdent.t * axiom   ) pp
val pp_modtype  : (EcIdent.t * tymod   ) pp
val pp_module   : module_expr pp
val pp_export   : EcPath.path pp
val pp_theory   : (EcIdent.t * ctheory) pp
