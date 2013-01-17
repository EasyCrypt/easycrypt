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

val pretty     : Pprint.document -> unit
val pp_located : Location.t -> 'a pp -> 'a pp
val pp_of_pr   : 'a pr -> 'a pp

(* -------------------------------------------------------------------- *)
module type IPrettyPrinter = sig
  type t                                (* ident-2-path *)

  val short_ident : t -> EcIdent.t -> EcPath.path

  (* ------------------------------------------------------------------ *)
  val pr_type     : t -> ?vmap:NameGen.t -> ty pr
  val pr_dom      : t -> EcTypes.dom pr
  val pr_typedecl : t -> (EcIdent.t * tydecl  ) pr
  val pr_opdecl   : t -> (EcIdent.t * operator) pr
  val pr_axiom    : t -> (EcIdent.t * axiom   ) pr
  val pr_modtype  : t -> (EcIdent.t * tymod   ) pr
  val pr_module   : t -> module_expr pr
  val pr_export   : t -> EcPath.path pr
  val pr_theory   : t -> (EcIdent.t * ctheory) pr
  val pr_expr     : t -> tyexpr pr
  
  (* ------------------------------------------------------------------ *)
  val pp_type     : t -> ?vmap:NameGen.t -> ty pp
  val pp_dom      : t -> EcTypes.dom pp
  val pp_typedecl : t -> (EcIdent.t * tydecl  ) pp
  val pp_opdecl   : t -> (EcIdent.t * operator) pp
  val pp_axiom    : t -> (EcIdent.t * axiom   ) pp
  val pp_modtype  : t -> (EcIdent.t * tymod   ) pp
  val pp_module   : t -> module_expr pp
  val pp_export   : t -> EcPath.path pp
  val pp_theory   : t -> (EcIdent.t * ctheory) pp
  val pp_expr     : t -> tyexpr pp
end

(* -------------------------------------------------------------------- *)
module type IIdentPrinter = sig
  type t

  val short_ident : t -> EcIdent.t -> EcPath.path
end

(* -------------------------------------------------------------------- *)
module EcPP : functor (M : IIdentPrinter) ->
  IPrettyPrinter with type t = M.t

(* -------------------------------------------------------------------- *)
module EcRawPP : sig
  (* ------------------------------------------------------------------ *)
  val pr_type     : ?vmap:NameGen.t -> ty pr
  val pr_dom      : EcTypes.dom pr
  val pr_typedecl : (EcIdent.t * tydecl  ) pr
  val pr_opdecl   : (EcIdent.t * operator) pr
  val pr_axiom    : (EcIdent.t * axiom   ) pr
  val pr_modtype  : (EcIdent.t * tymod   ) pr
  val pr_module   : module_expr pr
  val pr_export   : EcPath.path pr
  val pr_theory   : (EcIdent.t * ctheory) pr
  val pr_expr     : tyexpr pr
  
  (* ------------------------------------------------------------------ *)
  val pp_type     : ?vmap:NameGen.t -> ty pp
  val pp_dom      : EcTypes.dom pp
  val pp_typedecl : (EcIdent.t * tydecl  ) pp
  val pp_opdecl   : (EcIdent.t * operator) pp
  val pp_axiom    : (EcIdent.t * axiom   ) pp
  val pp_modtype  : (EcIdent.t * tymod   ) pp
  val pp_module   : module_expr pp
  val pp_export   : EcPath.path pp
  val pp_theory   : (EcIdent.t * ctheory) pp
  val pp_expr     : tyexpr pp

  val pp_path    : EcPath.path pp
  val pp_qsymbol : qsymbol pp
end
