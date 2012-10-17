(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
(** Functions about logic (build terms, etc)                                  *)
(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
type inv = (Fol.pred, Fol.pred * Fol.pred * Fol.pred) AstLogic.g_inv
val build_inv_spec : inv -> Ast.fct -> Ast.fct -> Fol.pred * Fol.pred
val build_inv_oracle_spec : inv -> Ast.fct -> Ast.fct -> Fol.pred * Fol.pred
val bound_random : Fol.lv_side -> Fol.term -> Ast.random -> Fol.pred

(* ~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~~ *)
