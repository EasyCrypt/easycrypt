(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** Global environment. Keeps everything about games, functions, etc. *)
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

open EcUtil
open Ast

type why_export =
  | WE_type of Ast.tdef
  | WE_cnst of Ast.const_body
  | WE_op of Ast.oper_body
  | WE_pred of Fol.predicate

val why_export : why_export list ref

(** General structure for register a new global element that need 
 * to be save for the undo/restore mechanism *)
type register = {
  r_save : int -> unit;
  r_restore : int -> unit;
}


(** All global variable that need to be save must call 
 * to add_register for register *)
val add_register : (int -> unit) -> (int -> unit) -> unit

val save_init_global : unit -> unit

val save_global : unit -> unit 

val restore_global : int -> unit

val add_list_register : 'a list ref -> unit

val cnst_list : const_body list ref

val set_timeout : int -> unit
val get_timeout : unit -> int
val withproof : unit -> bool
val set_withproof : bool -> unit
val change_withproof : unit -> unit

val get_num_instr : unit -> int


(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Variables }
*)

(** Variable environment *)
type venv

val empty_venv : unit -> venv
val game_venv : game -> venv
val fun_pre_venv : Ast.fct -> venv
val fun_post_venv : Ast.fct -> venv
val fun_local_venv : Ast.fct -> venv

val add_var : venv -> pos -> string -> type_exp -> venv * Ast.var
val fresh_var : venv -> string -> Ast.type_exp -> venv * Ast.var
val find_var : venv -> string -> Ast.var

(** compare that all the names exist in both env *)
val eq_env : venv -> venv -> bool

val iter_venv : (string -> Ast.var -> unit) -> venv -> unit

type lvenv

val iter_lvenv : (string -> Fol.lvar -> unit) -> lvenv -> unit

val empty_lvenv : unit -> lvenv
val add_lvar : lvenv -> string -> type_exp -> lvenv * Fol.lvar
val find_lvar : lvenv -> string -> Fol.lvar
val lvenv_of_venv : venv -> Fol.lv_side -> lvenv

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Add things in tables}
    * All these functions [add_xxx] first check if it is correct to add that name
    * in the environment, and raise PosError if not.
*)


val add_type : tdef -> unit

val add_cnst : const_body -> unit

(** @raise PosError if operator is already defined with the same type. *)
val add_op : ?prob:bool -> oper_body -> unit

val add_adv : adversary -> unit

val add_axiom : bool -> string -> Fol.pred -> unit
val set_all_axiom : bool -> unit

val set_axiom : string list -> unit
val unset_axiom : string list -> unit
val add_predicate : string -> Fol.lvar list * Fol.pred -> unit
val add_apredicate : string -> Ast.type_exp list -> unit

val add_popspec : string -> Fol.pop_spec -> unit
val find_popspec : string -> Fol.pop_spec

val add_pop_aspec : string -> Fol.pop_aspec -> unit
val find_pop_aspec : string -> Fol.pop_aspec

val add_fct : pos -> string -> vars_decl -> type_exp -> fct_body -> fct

val add_global : pos -> string -> type_exp -> unit

val start_game : string -> pos -> unit
val close_game : unit -> unit
val abort_game : unit -> unit
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Finding things}
    All these functions [find_xxx] can raise not found *)

val find_primitive_type : string -> type_exp
val find_type : string -> pos -> tdef

val find_cst : string -> const_body
val find_predicate : string -> Fol.predicate


(** raised by [find_op] *)
exception OpNotFound of (string * type_exp list)

(** Notice that we can have several operators with the same name,
    * but with different types.
    * @raise OpNotFound when this name is not defined for these types.
    * *)
val find_op : ?prob:bool -> pos -> string -> type_exp list ->  oper * type_exp

val find_adv : string -> pos -> adversary

val find_game : string -> game

val cur_game : string -> game

(** @raise Not_found when the function name is not in the game. *)
val find_fct_game : string -> game -> fct
(** Same as find_fct_game but in the current game.
    @raise Not_found when the function name is not registered. *)
val find_fct : string -> fct

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

val iter_cnst : (const_body -> unit) -> unit
val fold_cnst : ('a -> const_body -> 'a) -> 'a -> 'a

val iter_types : (tdef -> unit) -> unit
val fold_types : ('a -> tdef -> 'a) -> 'a -> 'a

val iter_ops : (oper_body -> unit) -> unit
val fold_ops : ('a -> oper_body -> 'a) -> 'a -> 'a

val iter_game : (string -> game -> unit) -> unit
val fold_game : (string -> game -> 'a -> 'a) -> 'a -> 'a

val iter_adv : (string -> adversary -> unit) -> unit
val fold_adv : (string -> adversary -> 'a -> 'a) -> 'a -> 'a

val iter_axioms : 
    (string * (bool ref * Fol.pred * Fol.why3_axiom) -> unit) -> unit

(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)
(** {2 Predefined operators} *)

val op_int_le : oper
val op_int_lt : oper
val op_int_add : oper
val op_int_sub : oper
val op_int_mul : oper
val op_int_pow : oper

val bool_and : oper
val bool_not : oper

val op_fst : type_exp -> oper
val op_snd : type_exp -> oper
val op_upd_map : type_exp -> oper
val op_get_map : type_exp -> oper
val op_length_list : type_exp -> oper
val op_in_list : type_exp -> oper 


val op_real_of_int : oper
val op_real_of_bool : oper
val op_real_add : oper
val op_real_mul : oper
val op_real_sub : oper
val op_real_div : oper
val op_real_pow : oper
val op_real_le : oper
val op_real_eq : oper
(*~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~*)

val check_fv : venv -> EcTerm.Vset.t -> bool


(*  *)

val rzero : Fol.term
val rone : Fol.term
val itr : int -> Fol.term

val find_and_show_cnst  : string -> unit
val find_and_show_op    : string -> unit
val find_and_show_pop   : string -> unit
val find_and_show_adv   : string -> unit

val find_and_show_axiom : string -> unit
val find_and_show_pred  : string -> unit
val find_and_show_type  : string -> unit
val find_and_show_game  : string -> unit
val find_and_show_fct   : string*string -> unit

val print_set_axiom : bool -> unit
val print_all_axiom : unit -> unit 
val print_all_op    : unit -> unit
val print_all_cnst  : unit -> unit
val print_all_pred  : unit -> unit
val print_all_type  : unit -> unit


(** Bitstring *)
val add_bitstring : Ast.cst_exp -> unit
