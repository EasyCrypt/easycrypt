(* -------------------------------------------------------------------- *)
open EcPath
open EcTypes
open EcModules

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
