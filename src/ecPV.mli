(* -------------------------------------------------------------------- *)
open EcPath
open EcTypes
open EcDecl
open EcModules
open EcMemory
open EcEnv
open EcFol

(* -------------------------------------------------------------------- *)
module Mpv : sig 
  type ('a,'b) t
   val empty : ('a,'b) t

  val add : env -> prog_var -> 'a -> ('a,'b) t -> ('a,'b) t

  val add_glob : env -> mpath -> 'b -> ('a,'b) t -> ('a,'b) t

  val find : env -> prog_var -> ('a,'b) t -> 'a

  val find_glob : env -> mpath -> ('a,'b) t -> 'b

  val issubst : env -> (expr, unit) t -> instr list -> instr list

end 

module PVM : sig
 
  type subst

  val empty : subst

  val add : env -> prog_var -> EcIdent.t -> form -> subst -> subst

  val add_glob : env -> mpath -> EcIdent.t -> form -> subst -> subst

  val find : env -> prog_var -> memory -> subst -> form

  val subst   : env -> subst -> form  -> form

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
