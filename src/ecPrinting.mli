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

  (* ------------------------------------------------------------------ *)
  val pr_type     : t -> ?vmap:NameGen.t -> ty pr
  val pr_expr     : t -> tyexpr pr
  val pr_dom      : t -> EcTypes.dom pr
  val pr_typedecl : t -> (EcPath.path * tydecl     ) pr
  val pr_opdecl   : t -> (EcPath.path * operator   ) pr
  val pr_axiom    : t -> (EcPath.path * axiom      ) pr
  val pr_modtype  : t -> (EcPath.path * tymod      ) pr
  val pr_module   : t -> (EcPath.path * module_expr) pr
  val pr_theory   : t -> (EcPath.path * ctheory    ) pr
  val pr_export   : t -> EcPath.path pr
  
  (* ------------------------------------------------------------------ *)
  val pp_type     : t -> ?vmap:NameGen.t -> ty pp
  val pp_expr     : t -> tyexpr pp
  val pp_dom      : t -> EcTypes.dom pp
  val pp_typedecl : t -> (EcPath.path * tydecl     ) pp
  val pp_opdecl   : t -> (EcPath.path * operator   ) pp
  val pp_axiom    : t -> (EcPath.path * axiom      ) pp
  val pp_modtype  : t -> (EcPath.path * tymod      ) pp
  val pp_module   : t -> (EcPath.path * module_expr) pp
  val pp_theory   : t -> (EcPath.path * ctheory    ) pp
  val pp_export   : t -> EcPath.path pp
end

(* -------------------------------------------------------------------- *)
module type IIdentPrinter = sig
  type t

  val add_ty    : t -> EcPath.path -> t 
  val add_local : t -> EcIdent.t -> t
  val add_pvar  : t -> EcPath.path -> t 
  val add_fun   : t -> EcPath.path -> t 
  val add_mod   : t -> EcPath.path -> t 
  val add_modty : t -> EcPath.path -> t 
  val add_op    : t -> EcPath.path -> t 
  val add_ax    : t -> EcPath.path -> t 
  val add_th    : t -> EcPath.path -> t 

  val tv_symb    : t -> EcIdent.t   -> EcSymbols.symbol
  val ty_symb    : t -> EcPath.path -> EcSymbols.qsymbol
  val local_symb : t -> EcIdent.t   -> EcSymbols.symbol
  val pv_symb    : t -> EcPath.path -> int option -> EcSymbols.qsymbol
  val fun_symb   : t -> EcPath.path -> EcSymbols.qsymbol
  val mod_symb   : t -> EcPath.path -> EcSymbols.qsymbol
  val modty_symb : t -> EcPath.path -> EcSymbols.qsymbol
  val op_symb    : t -> EcPath.path -> EcSymbols.qsymbol
  val ax_symb    : t -> EcPath.path -> EcSymbols.qsymbol
  val th_symb    : t -> EcPath.path -> EcSymbols.qsymbol
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
