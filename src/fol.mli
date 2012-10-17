
(** {2 FOL types} *)

(** {3 Variables} *)

type lv_side = FVleft | FVright

type lv_base =
  | FVpgVar of Ast.var * lv_side
  | FVlogic of string * Ast.type_exp
(* type lv_base *)

type lvar = { lv_base: lv_base; lv_id: UID.lvar }
(* type lvar *)

module FVset : sig
  include Set.S with type elt = lvar
  val compare : t -> t -> int
end



val pp_lvar : Format.formatter -> lvar -> unit
val pp_lvar_why : Format.formatter -> lvar -> unit

val lvar_of_var : Ast.var -> lv_side -> lvar
val logic_lvar : string -> Ast.type_exp -> lvar

val lv_type : lvar ->  Ast.type_exp
val lv_name : lvar -> string

(** {3 Terms} *)

type term = (lvar,lvar) Ast.v_exp

val term_of_exp : lv_side -> Ast.var_exp -> term


(** {3 Predicates} *)
type predicate 
type triggers 

type pred =
  | Ptrue
  | Pfalse
  | Pnot of pred
  | Pand of pred * pred
  | Por of pred * pred
  | Pimplies of pred * pred
  | Piff of pred * pred
  | Pif of bool * term * pred * pred
  (* the [bool] is a split information (see. [WhyCmds.check_split_opt]) *)
  | Pforall of lvar * triggers * pred
  | Pexists of lvar * triggers * pred
  | Plet of lvar list * term * pred
  | Papp of predicate * term list
  | Pterm of term

val nb_var_in_pred : lvar -> pred -> int 

val eq_term : term -> term -> bool
val eq_pred : pred -> pred -> bool

val pred_of_exp : lv_side -> Ast.var_exp -> pred

val fv_pred : pred -> EcTerm.Vset.t *EcTerm.Vset.t

val free_term_vars : term -> FVset.t
val free_pred_vars : pred -> FVset.t


(** {2 Smart Constructors} *)

val peq : term -> term -> pred
val ple_int : term -> term -> pred
val plt_int : term -> term -> pred
val ple_real : term -> term -> pred
val plt_real : term -> term -> pred

val pred_of_term : term -> pred
val pand :  pred -> pred -> pred
val pands : pred list -> pred
val pimplies : pred -> pred -> pred
val papp : predicate * term list -> pred
val por : pred -> pred -> pred
val pxor : pred -> pred -> pred
val pors : pred list -> pred -> pred
val piff : pred -> pred -> pred
val pnot : pred -> pred
val pif :  ?split_info:bool -> term -> pred -> pred -> pred

val pclos : pred -> pred

val eq_lvar : lvar -> lvar -> bool
(* I generalized the type so I can used it with exp *)
val change_vars_in_var_exp: ('a -> (('var,'c, 'a, 'd, 'b) Ast.g_exp as 'b) option) 
  -> 'b -> 'b

val let_pred : ?fresh:bool -> lvar list -> term -> pred -> pred
val let_pred_opt : ?fresh:bool -> lvar -> term option -> pred -> pred

val forall_pred_with_var : ?fresh:bool -> lvar -> pred -> (lvar * pred)
val forall_pred : ?fresh:bool -> lvar -> pred -> pred
val exists_pred : ?fresh:bool -> lvar -> pred -> pred

val forall_trigger : 
    lvar list -> (term * Ast.type_exp) list list -> pred -> pred
val exists_trigger : 
    lvar list -> (term * Ast.type_exp) list list -> pred -> pred

val peq_exp : Ast.var_exp -> Ast.var_exp -> pred
val peq_vars : Ast.var -> Ast.var -> pred
val peq_lvars : Ast.var list -> Ast.var list -> pred


val remove_dep : EcTerm.Vset.t -> EcTerm.Vset.t -> pred -> pred

(** {2 Substitution} *)
val subst_var_in_term : lvar -> term -> term -> term

val subst_in_pred : lvar -> term -> pred -> pred

val subst_vars_in_pred : (lvar -> term option) -> pred -> pred

(* val subst_vars_in_exp : (var * term) list -> exp -> term *)

(*
  val mk_renaming : Ast.var list -> lv_side -> lvar EcTerm.renaming
  val subst_vars_in_pred : (lvar -> term option) -> pred -> pred
  val rename_pred : lvar EcTerm.renaming -> pred -> pred
*)

(** change the program variables in FVright by program variables in FVleft,
    assert false in the pred contains variables in FVleft *)
val set_left : pred -> pred

(** {2 Destructor} *)
val split_pred : pred -> pred list

(** {2 mkeq} *)

val mkeq_params : Ast.fct -> Ast.fct -> pred
val mkeq_result : Ast.fct -> Ast.fct -> pred

(** {2 Pretty printing} *)

val pp_term : int -> Format.formatter -> term -> unit 

val pp_pred : Format.formatter -> pred -> unit
(* val pp_predicate : Format.formatter -> predicate -> unit *)

(** {2 Adding new predicate} *)
val mk_predicate : string -> lvar list * pred -> predicate

val mk_apredicate : string -> Ast.type_exp list -> predicate

val predicate_name : predicate -> string

val predicate_type : predicate -> Ast.type_exp list

val logic_decl : predicate -> Why3.Decl.logic_decl

val set_opacity : bool -> predicate -> unit
val opacity : predicate -> bool

val unfold_pred : string list -> pred -> pred

val is_eq_pred : predicate -> bool

val pp_predicate : Format.formatter -> predicate -> unit
(** Buildint why3 axiom *)

type why3_axiom = Why3.Decl.prsymbol * Why3.Term.term

val mk_axiom : string -> pred -> why3_axiom


type pop_spec = 
    (lvar list * Ast.var list) *
      (lvar * Ast.exp * Ast.exp option) *
      (lvar * Ast.exp * Ast.exp option) *
      (pred * pred * (term * term) option)

type pop_aspec =
    (lvar list * Ast.type_exp list) *
      (lvar * Ast.oper * lvar list) *
      (pred * pred)


val remove_let : pred -> pred
val find_same : pred -> (Ast.var * Ast.var) list
val simplify_equality : pred -> pred
