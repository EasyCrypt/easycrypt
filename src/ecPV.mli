(* -------------------------------------------------------------------- *)
open EcPath
open EcTypes
open EcDecl
open EcModules
open EcMemory
open EcEnv
open EcFol

(* -------------------------------------------------------------------- *)
module PVM : sig
  type mem_sel = 
  | MSvar of prog_var
  | MSmod of EcPath.mpath (* Only abstract module *)

  type 'a subst

  val empty : 'a subst

  val pvm : env -> prog_var -> 'a -> mem_sel * 'a

  val add : env -> prog_var -> EcIdent.t -> 'a -> 'a subst -> 'a subst

  val add_glob : env -> mpath -> EcIdent.t -> 'a -> 'a subst -> 'a subst

  val merge : 'a subst -> 'a subst -> 'a subst

  val find : env -> prog_var -> memory -> 'a subst -> 'a

  val check_pv      : env -> prog_var -> EcIdent.t -> 'a subst -> mem_sel * EcIdent.t
  val check_binding : EcIdent.t -> form subst -> unit

  val subst   : env -> form  subst -> form  -> form
  val esubst  : env -> memory -> expr subst -> expr  -> expr
  val isubst  : env -> memory -> expr subst -> instr -> instr
  val issubst : env -> memory -> expr subst -> instr list -> instr list
  val ssubst  : env -> memory -> expr subst -> stmt  -> stmt

  val subst1  : env -> prog_var -> EcIdent.t -> form -> form -> form
end

(* -------------------------------------------------------------------- *)
module PV : sig
  module M : EcMaps.Map.S with type key = prog_var

  type pv_fv = private {
    pv   : ty M.t;                    (* The key are in normal form *)
    glob : EcPath.Sm.t;               (* The set of abstract module *)
  }

  val empty : pv_fv

  val is_empty : pv_fv -> bool

  val add      : env -> prog_var -> ty -> pv_fv -> pv_fv
  val add_glob : env -> mpath -> pv_fv -> pv_fv

  val remove : env -> prog_var -> pv_fv -> pv_fv

  val union : env -> pv_fv -> pv_fv -> pv_fv
  val diff  : env -> pv_fv -> pv_fv -> pv_fv
  val inter : env -> pv_fv -> pv_fv -> pv_fv

  val disjoint : env -> pv_fv -> pv_fv -> bool

  val elements : pv_fv -> (prog_var * ty) list * mpath list

  val mem_pv   : prog_var -> pv_fv -> bool
  val mem_glob : mpath -> pv_fv -> bool

  val fv : env -> EcIdent.t -> form -> pv_fv

  val pp : env -> Format.formatter -> pv_fv -> unit

  val disjoint_g : env -> mpath -> mpath -> bool

  val check : env -> pv_fv -> pv_fv -> unit
end
