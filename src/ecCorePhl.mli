(* -------------------------------------------------------------------- *)
open EcSymbols
open EcParsetree
open EcPath
open EcTypes
open EcMemory
open EcModules
open EcFol
open EcMetaProg.Zipper
open EcEnv
open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
type 'a sdestr_t  = string -> stmt -> 'a * stmt
type 'a sdestr2_t = string -> stmt -> stmt -> 'a * 'a * stmt * stmt

(* -------------------------------------------------------------------- *)
val s_first_asgn    : (lvalue * expr) sdestr_t
val s_first_asgns   : (lvalue * expr) sdestr2_t
val s_first_rnd     : (lvalue * expr) sdestr_t
val s_first_rnds    : (lvalue * expr) sdestr2_t
val s_first_call    : (lvalue option * xpath * expr list) sdestr_t
val s_first_calls   : (lvalue option * xpath * expr list) sdestr2_t
val s_first_if      : (expr * stmt * stmt) sdestr_t
val s_first_ifs     : (expr * stmt * stmt) sdestr2_t
val s_first_while   : (expr * stmt) sdestr_t
val s_first_whiles  : (expr * stmt) sdestr2_t
val s_first_assert  : expr sdestr_t
val s_first_asserts : expr sdestr2_t

(* -------------------------------------------------------------------- *)
val s_last_asgn    : (lvalue * expr) sdestr_t
val s_last_asgns   : (lvalue * expr) sdestr2_t
val s_last_rnd     : (lvalue * expr) sdestr_t
val s_last_rnds    : (lvalue * expr) sdestr2_t
val s_last_call    : (lvalue option * xpath * expr list) sdestr_t
val s_last_calls   : (lvalue option * xpath * expr list) sdestr2_t
val s_last_if      : (expr * stmt * stmt) sdestr_t
val s_last_ifs     : (expr * stmt * stmt) sdestr2_t
val s_last_while   : (expr * stmt) sdestr_t
val s_last_whiles  : (expr * stmt) sdestr2_t
val s_last_assert  : expr sdestr_t
val s_last_asserts : expr sdestr2_t

(* -------------------------------------------------------------------- *)
val t_as_hoareF   : form -> hoareF
val t_as_hoareS   : form -> hoareS
val t_as_bdHoareF : form -> bdHoareF
val t_as_bdHoareS : form -> bdHoareS
val t_as_equivF   : form -> equivF
val t_as_equivS   : form -> equivS
val t_as_eagerF   : form -> eagerF
(* -------------------------------------------------------------------- *)
val get_pre  : form -> form
val get_post : form -> form
val set_pre  : pre:form -> form -> form

(* -------------------------------------------------------------------- *)
val t_hS_or_bhS_or_eS : ?th:tactic -> ?tbh:tactic -> ?te:tactic -> tactic
val t_hF_or_bhF_or_eF : ?th:tactic -> ?tbh:tactic -> ?te:tactic -> tactic

(* -------------------------------------------------------------------- *)
type 'a code_tx_t =
     LDecl.hyps -> 'a -> form * form -> memenv * stmt
  -> memenv * stmt * form list

type zip_t = 
     LDecl.hyps -> form * form -> memenv -> zipper
  -> memenv * zipper * form list

val t_zip : zip_t -> codepos code_tx_t

val t_fold : (LDecl.hyps, memenv) folder -> codepos code_tx_t

val t_code_transform :
      bool option -> ?bdhoare:bool -> 'state
  -> (bool option -> EcBaseLogic.rule)
  -> 'state code_tx_t
  -> tactic

(* -------------------------------------------------------------------- *)
val s_split_i : string -> int -> stmt -> instr list * instr * instr list
val s_split   : string -> int -> stmt -> instr list * instr list
val s_split_o : string -> int option -> stmt -> instr list * instr list

(* -------------------------------------------------------------------- *)
val id_of_pv : prog_var -> memory -> EcIdent.t
val id_of_mp : mpath    -> memory -> EcIdent.t

(* -------------------------------------------------------------------- *)
val fresh_pv : memenv -> variable -> memenv * symbol

(* -------------------------------------------------------------------- *)
type lv_subst_t = (lpattern * form) * (prog_var * memory * form) list

val mk_let_of_lv_substs : EcEnv.env -> (lv_subst_t list * form) -> form

val lv_subst : memory -> lvalue -> form -> lv_subst_t

val subst_form_lv : EcEnv.env -> memory -> lvalue -> form -> form -> form

(* -------------------------------------------------------------------- *)
type ai_t = mpath * xpath * oracle_info * funsig

val abstract_info  : EcEnv.env -> xpath -> ai_t
val abstract_info2 : EcEnv.env -> xpath -> xpath -> ai_t * ai_t

(* -------------------------------------------------------------------- *)
val mk_inv_spec : EcEnv.env -> form -> xpath -> xpath -> form

(* -------------------------------------------------------------------- *)
val generalize_subst :
     EcEnv.env -> memory -> (prog_var * ty) list -> mpath list
  -> (EcIdent.t * gty) list * (form, form) EcPV.Mpv.t

val generalize_mod : EcEnv.env -> EcIdent.t -> EcPV.PV.t -> form -> form
