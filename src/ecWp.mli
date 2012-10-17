exception Wp_random
exception Wp_no_random
exception Wp_call
exception Wp_no_calls
exception Wp_no_asgn
exception Wp_wrong_equiv of ((Ast.fct * Ast.fct) * (Ast.fct * Ast.fct))
exception Wp_nothing_done
exception Sp_nothing_done

(** Process every assignments in s1 and s2.
    * @raise Wp_no_asgn when their is no assignment to process. *)
val wp_asgn_fct : Ast.stmt -> Ast.stmt ->  Fol.pred ->
  Ast.stmt * Ast.stmt * Fol.pred

(** Process assignments and if in s1 and s2. Stop on random and calls.
    * @raise Wp_nothing_done when no progress as been done. *)
val wp_simpl_fct : Ast.stmt -> Ast.stmt ->  Fol.pred ->
  Ast.stmt * Ast.stmt * Fol.pred

val wp_simpl_fct_app : Ast.stmt -> Ast.stmt ->  Fol.pred ->
  Ast.stmt * Ast.stmt * Fol.pred

val wp_call1 :
  Ast.lasgn -> Ast.fct -> Ast.exp list ->
  Fol.pred -> Fol.pred -> Fol.pred -> (Fol.lvar list * Fol.pred)

(** @raise Wp_wrong_equiv with (eq_f1, eq_f2), (called_f1, called_f2)) *)
val wp_call_equiv_fct : AstLogic.equiv ->
  Ast.stmt -> Ast.stmt ->  Fol.pred ->
  (Fol.term * Fol.term) option ->
  (Fol.lvar list * Fol.lvar list) * Ast.stmt * Ast.stmt * Fol.pred * (Fol.term * Fol.term) option

(** @raise Wp_no_random when one of the stmt list don't start with a random
    * assignment. *)
val wp_rnd_fct : (Fol.lvar * Fol.term) AstLogic.rnd_bij_info ->
  Ast.stmt -> Ast.stmt ->  Fol.pred ->
  (Fol.term * Fol.term) option ->
  Fol.lvar * Ast.stmt * Ast.stmt * Fol.pred * (Fol.term * Fol.term) option

(** @raise Wp_no_random when one of the stmt list don't start with a random
    * assignment. *)
val wp_rnd_disj_fct : ApiTypes.side -> Ast.stmt -> Ast.stmt -> Fol.pred ->
  (Fol.term * Fol.term) option ->
  Fol.lvar * Ast.stmt * Ast.stmt * Fol.pred * (Fol.term * Fol.term) option


exception Sp_no_random
val sp_rnd_fct : (Fol.lvar * Fol.term) AstLogic.rnd_bij_info ->
  Ast.stmt -> Ast.stmt ->  Fol.pred ->
  (Fol.term * Fol.term) option ->
  Fol.lvar * Ast.stmt * Ast.stmt * Fol.pred * (Fol.term * Fol.term) option

val sp_rnd_disj_fct : ApiTypes.side -> Ast.stmt -> Ast.stmt -> Fol.pred ->
  (Fol.term * Fol.term) option ->
  Fol.lvar * Ast.stmt * Ast.stmt * Fol.pred * (Fol.term * Fol.term) option



(** Similar to [wp_asgn] but used for [return exp_opt;] *)
val wp_return :
  Fol.lv_side -> Ast.var -> Ast.var_exp option -> Fol.pred -> Fol.pred

(** [wp_call x1 f1 args1 x2 f2 args2 pre post p] *)
val wp_call :  Ast.lasgn -> Ast.fct -> Ast.var_exp list ->
  Ast.lasgn -> Ast.fct -> Ast.var_exp list ->
  Fol.pred -> Fol.pred ->
  Fol.pred -> 
  (Fol.term * Fol.term) option ->
  (Fol.term * Fol.term) option ->
  ((Fol.lvar list * Fol.lvar list) * Fol.pred * (Fol.term * Fol.term) option)




val reduce_app : (Fol.term*Fol.term) option -> 
  (Fol.term*Fol.term) option -> 
  (Fol.term*Fol.term) option 

val sp_simpl_fct : Ast.stmt -> Ast.stmt ->  Fol.pred ->
  Ast.stmt * Ast.stmt * Fol.pred

