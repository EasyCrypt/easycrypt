(* -------------------------------------------------------------------- *)
open EcParsetree
open EcUid
open EcLocation
open EcPath
open EcTypes
open EcModules
open EcFol
open EcUnify
open EcEnv
open EcLogic

(* -------------------------------------------------------------------- *)
val unienv_of_hyps : LDecl.hyps -> unienv

val process_tyargs :
  LDecl.hyps -> ptyannot option -> EcUnify.tvar_inst option

val process_named_pterm :
  'a -> LDecl.hyps -> pqsymbol * ptyannot option
  ->   [ `Global of EcPath.path
       | `Local  of EcIdent.t ]
     * ty list * unienv * form

val process_pterm :
     'a -> ('b -> form) -> LDecl.hyps -> 'b EcParsetree.fpattern
  ->   [ `Cut    of EcFol.form
       | `Global of EcPath.path
       | `Local  of EcIdent.t ]
     * ty list * unienv * form

val trans_pterm_argument :
     LDecl.hyps -> EcUnify.unienv -> fpattern_arg located
  ->   [ `FormOrMod of form option * (mpath * module_sig) option
       | `Memory    of EcIdent.t ]
     option

type pterm_parg =
  [ `FormOrMod of form option * (mpath * module_sig) option
  | `Memory    of EcIdent.t ]

type 'a pterm_arg =
  [ `KnownMem   of EcIdent.t * EcIdent.t
  | `KnownMod   of EcIdent.t * (mpath * module_sig)
  | `KnownVar   of EcIdent.t * form
  | `SideCond   of EcFol.form
  | `UnknownVar of EcIdent.t * 'a ]

val evmap_of_pterm_arguments : ('a pterm_arg) list -> form EcMetaProg.evmap

val check_pterm_arg_for_ty :
  LDecl.hyps -> gty option -> fpattern_arg located -> app_arg

val check_pterm_argument :
  LDecl.hyps -> EcUnify.unienv -> form
  -> pterm_parg option
  -> form * ty pterm_arg

val check_pterm_arguments :
  LDecl.hyps -> EcUnify.unienv -> form
  -> pterm_parg option list
  -> form * ty pterm_arg list

val can_concretize_pterm_arguments :
  unienv * form EcMetaProg.evmap -> ('a pterm_arg) list -> bool

val concretize_pterm_arguments :
  (uid -> ty option) * form EcMetaProg.evmap -> ('a pterm_arg) list -> app_arg list

val concretize_form :
  (uid -> ty option) * form EcMetaProg.evmap -> form -> form

val concretize_pterm :
  (uid -> ty option) * form EcMetaProg.evmap -> ('a pterm_arg) list -> form -> form

(* -------------------------------------------------------------------- *)
val process_form_opt : LDecl.hyps -> pformula -> ty option -> form
val process_form     : LDecl.hyps -> pformula -> ty -> form
val process_formula  : LDecl.hyps -> pformula -> form
val process_exp      : LDecl.hyps -> [`InProc|`InOp] -> pexpr -> ty option -> expr

(* -------------------------------------------------------------------- *)
val process_mkn_apply :
     ('a -> form)
  -> 'a fpattern
  -> goal
  -> goal * int list
