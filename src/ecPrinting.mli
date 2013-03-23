(* -------------------------------------------------------------------- *)
open EcSymbols
open EcFormat
open EcPath
open EcUidgen
open EcParsetree
open EcMemory
open EcTypes
open EcDecl
open EcModules
open EcTheory

(* -------------------------------------------------------------------- *)
type 'a pr = 'a -> Pprint.document

val pretty     : Pprint.document -> unit
val pp_of_pr   : 'a pr -> 'a pp

(* -------------------------------------------------------------------- *)
module type IPrettyPrinter = sig
  type t                                (* ident-2-path *)
  val init : EcEnv.env * EcEnv.env list -> t
  val mono : EcEnv.env -> t

  (* ------------------------------------------------------------------ *)
  val pr_type     : t -> ?vmap:NameGen.t -> ty pr
  val pr_expr     : t -> expr pr
  val pr_form     : t -> EcFol.form pr
  val pr_dom      : t -> EcTypes.dom pr
  val pr_typedecl : t -> (EcPath.path * tydecl     ) pr
  val pr_opdecl   : t -> (EcPath.path * operator   ) pr
  val pr_axiom    : t -> (EcPath.path * axiom      ) pr
  val pr_modsig   : t -> (EcPath.path * module_sig)  pr
  val pr_module   : t -> (EcPath.path * module_expr) pr
  val pr_theory   : t -> (EcPath.path * ctheory    ) pr
  val pr_export   : t -> EcPath.path pr
  val pr_lgoal    : ?n:int -> t -> EcBaseLogic.l_decl pr

  (* ------------------------------------------------------------------ *)
  val pp_type     : t -> ?vmap:NameGen.t -> ty pp
  val pp_expr     : t -> expr pp
  val pp_form     : t -> EcFol.form pp
  val pp_dom      : t -> EcTypes.dom pp
  val pp_typedecl : t -> (EcPath.path * tydecl     ) pp
  val pp_opdecl   : t -> (EcPath.path * operator   ) pp
  val pp_axiom    : t -> (EcPath.path * axiom      ) pp
  val pp_modsig   : t -> (EcPath.path * module_sig ) pp
  val pp_module   : t -> (EcPath.path * module_expr) pp
  val pp_theory   : t -> (EcPath.path * ctheory    ) pp
  val pp_export   : t -> EcPath.path pp
  val pp_lgoal    : t -> EcBaseLogic.l_decl pp
  val pp_fct_def  : t -> EcModules.function_def pp
end

(* -------------------------------------------------------------------- *)
module type IIdentPrinter = sig
  type t
  val init : (EcEnv.env * EcEnv.env list) -> t 

  val add_ty    : t -> EcPath.path -> t 
  val add_local : t -> EcIdent.t   -> t
  val add_pvar  : t -> EcPath.path -> t 
  val add_fun   : t -> EcPath.path -> t 
  val add_mod   : t -> EcPath.path -> t 
  val add_modty : t -> EcPath.path -> t 
  val add_op    : t -> EcPath.path -> t 
  val add_ax    : t -> EcPath.path -> t 
  val add_th    : t -> EcPath.path -> t 

  val string_of_ident : EcIdent.t -> string

  val tv_symb    : t -> EcIdent.t   -> EcSymbols.symbol
  val ty_symb    : t -> EcPath.path -> EcSymbols.qsymbol
  val local_symb : t -> EcIdent.t   -> EcSymbols.symbol
  val pv_symb    : t -> EcPath.mpath -> memory option -> EcSymbols.qsymbol
  val fun_symb   : t -> EcPath.mpath -> EcSymbols.qsymbol
  val mod_symb   : t -> EcPath.mpath -> EcSymbols.qsymbol
  val modty_symb : t -> EcPath.path -> EcSymbols.qsymbol
  val op_symb    : t -> EcPath.path -> EcTypes.ty list -> 
                    EcTypes.ty list option -> EcSymbols.qsymbol
  val ax_symb    : t -> EcPath.path -> EcSymbols.qsymbol
  val th_symb    : t -> EcPath.path -> EcSymbols.qsymbol
end

(* -------------------------------------------------------------------- *)
module MakePP : functor (M : IIdentPrinter) -> IPrettyPrinter
module EcPP   : IPrettyPrinter

(* -------------------------------------------------------------------- *)
module EcDebugPP : sig

  (* ------------------------------------------------------------------ *)
  val pr_type     : ?vmap:NameGen.t -> ty pr
  val pr_dom      : EcTypes.dom pr
  val pr_typedecl : (symbol * tydecl     ) pr
  val pr_opdecl   : (symbol * operator   ) pr
  val pr_axiom    : (symbol * axiom      ) pr
  val pr_modsig   : (symbol * module_sig ) pr
  val pr_module   : module_expr pr
  val pr_export   : EcPath.path pr
  val pr_theory   : (symbol * ctheory) pr
  val pr_expr     : expr pr
  val pr_form     : EcFol.form pr
  val pr_lgoal    : EcBaseLogic.l_decl pr

  (* ------------------------------------------------------------------ *)
  val pp_type     : ?vmap:NameGen.t -> ty pp
  val pp_dom      : EcTypes.dom pp
  val pp_typedecl : (symbol * tydecl     ) pp
  val pp_opdecl   : (symbol * operator   ) pp
  val pp_axiom    : (symbol * axiom      ) pp
  val pp_modsig   : (symbol * module_sig ) pp
  val pp_module   : module_expr pp
  val pp_export   : EcPath.path pp
  val pp_theory   : (symbol * ctheory) pp
  val pp_expr     : expr pp
  val pp_form     : EcFol.form pp
  val pp_lgoal    : EcBaseLogic.l_decl pp

  val pp_path    : EcPath.path pp
end
