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
 
  type t 

  val empty : t

  val is_empty : t -> bool

  val add      : env -> prog_var -> ty -> t -> t
  val add_glob : env -> mpath -> t -> t

  val remove   : env -> prog_var -> t -> t

  val diff     : t -> t -> t

  val interdep : env -> t -> t -> t
  val indep    : env -> t -> t -> bool
  val check_depend : env -> t -> mpath -> unit

  val elements : t -> (prog_var * ty) list * mpath list

  val mem_pv   : env -> prog_var -> t -> bool
  val mem_glob : env -> mpath -> t -> bool

  val fv       : env -> EcIdent.t -> form -> t

  val pp       : env -> Format.formatter -> t -> unit

end
