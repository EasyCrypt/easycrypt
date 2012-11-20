(** Function on {!Ast} terms *)

open EcUtil
open Ast


(** {2 Functions on types} *)

val seq_type : type_exp -> type_exp -> bool

val get_tuple : type_exp -> type_exp list
val is_type_bool : type_exp -> bool
(* [get_named_type s t] return [l] if [t = l s],
   raise Not_found otherwise *)
val get_named_type : string -> type_exp -> type_exp list

val mk_tvar : ?tvar_def:Ast.tvar_def -> string -> pos -> tvar
val eq_tvar : tvar -> tvar -> bool

val mk_tdef : string -> pos -> type_exp list -> type_exp option -> tdef

val eq_tdef_name : tdef -> tdef -> bool

val fv_type : type_exp -> tvar list
val fv_types : type_exp list -> tvar list


val subst_tvar : (tvar * type_exp) list -> type_exp -> type_exp

val type_of_random : random -> type_exp


(** {2 Functions over variables} *)

val eq_var : var -> var -> bool
val var_compare : var -> var -> int
val mk_local  : string -> type_exp -> pos -> var
val mk_global : string -> type_exp -> pos -> var

val fresh_var : var -> var

module Vset : sig
  include Set.S with type elt = var
  val pp : Format.formatter -> t -> unit
  val disjoint : t -> t -> bool
end

module Vset2 : Set.S with type elt = Ast.var * Ast.var

(** {2 Functions on operators} *)

val mk_op_body :
  string -> native_op option -> (string * bool) ->
  g_fct_sig -> (var list*var_exp) option -> bool -> pos -> 
  bool option -> int -> oper_body

val op_body : oper -> oper_body

val op_name : oper -> string

val op_native : oper -> native_op option

val op_why : oper -> string

val op_ac : oper -> bool

val op_prec : oper -> int

val is_infix : oper -> bool

val eq_op : oper -> oper -> bool

val instanciate_op : oper_body -> pos -> tvar list * g_fct_sig

val reset_poly : tvar list -> unit

val is_op : Ast.native_op -> oper -> bool

(** {2 Functions on expressions} *)

val fold_var_in_exp : 
  ('v -> 'a -> 'a) ->
  ('a -> 'b -> 'a) -> 'a ->
  (('v,'d,'b,'e,'c) Ast.g_exp as 'c) -> 'a

val map_var_in_exp :  
  ('v1 -> 'v2) -> 
  ('a -> (('v2, 'c, 'd, 'e, 'b) Ast.g_exp as 'b)) ->
  (('v1, 'c, 'a, 'e, 'f) Ast.g_exp as 'f) -> 'b

val g_eq_exp : ('v -> 'v -> bool) ->  ('b -> 'b -> bool) -> 
  (('v,'b) v_exp -> ('v,'b) v_exp -> bool)

val eq_exp : exp -> exp -> bool
val eq_random : random -> random -> bool
val is_uniform : random -> bool
val is_cnst_exp :('v,'b) v_exp -> bool
val is_cnst_rnd : random -> bool

val is_var_exp : ('v,'b) v_exp -> bool

val fv_exp : exp -> Vset.t
val fv_args : exp list -> Vset.t

(** {2 renaming of variables} *)

type 'v renaming = ('v * 'v) list

(* [mk_renaming vd] return (vd',r) where r is a renaming allowing
   to replace variable in vd by the fresh variables in vd' *)
val mk_renaming : var list -> var list * var renaming
val g_mk_renaming : ('v -> 'v) -> 'v list -> 'v list * 'v renaming

val rename_exp : 'b renaming -> ('v,'b) v_exp -> ('v,'b) v_exp

val subst_exp : (var * exp) list -> exp -> exp


(** {2 Functions on statements} *)

val rename_instr : var renaming -> instr -> instr
val rename_stmt  : var renaming -> stmt -> stmt

val modified_lasgn : lasgn  -> Vset.t
val modified_instr : instr -> Vset.t
val modified_stmt : stmt -> Vset.t

val read_lasgn : lasgn  -> Vset.t
val read_stmt : stmt -> Vset.t
val read_instr : instr -> Vset.t
val global_read_fct : fct -> Vset.t

val eq_instr : instr -> instr -> bool
val eq_stmt : stmt -> stmt -> bool

(** {2 Functions on functions}*)

exception UndefinedFct of fct
exception DefinedFct of fct

val eq_fct : fct -> fct -> bool
val is_defined_fct : fct -> bool

(** @raise UndefinedFct when [is_defined_fct] is false. *)
val check_defined_fct : fct -> unit

(** @raise UndefinedFct when [is_defined_fct] is false. *)
val fct_def : fct -> fct_def

(** @raise DefinedFct when [is_defined_fct]. *)
val fct_adv : fct -> adversary * fct list

val global_modified : fct_body -> Vset.t
val global_read : fct_body -> Vset.t


(** Recompute the type of an expression *)


val term_of_var : (Ast.var * Why3.Term.term) list -> Ast.var -> Why3.Term.term

val term_of_exp :
      (tvar * Why3.Ty.tvsymbol) list ->
      (var * Why3.Term.term) list ->
      var_exp -> Why3.Term.term

val form_of_exp :
    (tvar * Why3.Ty.tvsymbol) list ->
    (var * Why3.Term.term) list ->
    var_exp -> Why3.Term.term

val g_term_of_exp : 
    (Format.formatter -> ('b, 'c) v_exp -> unit) ->
    ((tvar * Why3.Ty.tvsymbol) list -> 'a -> 'b ->
      (tvar * Why3.Ty.tvsymbol) list * 'a * Why3.Term.vsymbol) ->
    ('a -> 'c -> Why3.Term.term) ->
    ((tvar * Why3.Ty.tvsymbol) list -> 'a ->
      ('b, 'c) v_exp -> Why3.Term.term) *
    ((tvar * Why3.Ty.tvsymbol) list -> 'a ->
      ('b, 'c) v_exp -> Why3.Term.term)

val add_why3_type :
    (tvar * Why3.Ty.tvsymbol) list ->
      Ast.type_exp -> (tvar * Why3.Ty.tvsymbol) list * Why3.Ty.ty
    
val add_why3_var : 
    (tvar * Why3.Ty.tvsymbol) list ->
      (Ast.var * Why3.Term.term) list ->
        Ast.var ->
          (tvar * Why3.Ty.tvsymbol) list *
            (Ast.var * Why3.Term.term) list * Why3.Term.vsymbol

val add_why3_vars :
    (tvar * Why3.Ty.tvsymbol) list ->
      (Ast.var * Why3.Term.term) list ->
        Ast.var list ->
          (tvar * Why3.Ty.tvsymbol) list *
            (Ast.var * Why3.Term.term) list * Why3.Term.vsymbol list 
    

val find_bitstring : cst_exp -> Why3.Ty.tysymbol * Why3.Ty.ty
val add_bitstring : cst_exp -> string
val mk_fsymbol : string -> type_exp list * type_exp -> Why3.Term.lsymbol
val decl_bitstring : Why3.Task.task -> Why3.Task.task 

(** lossless *)
val is_lossless_fun : fct -> bool
val is_lossless_stmt : stmt -> bool



