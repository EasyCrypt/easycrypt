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

  val check_npv : env -> prog_var -> ('a,'b) t -> unit

  val check_glob : env -> mpath -> ('a,'b) t -> unit 

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
    
  val of_mpv : (form,form) Mpv.t -> EcIdent.t -> subst

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

  val fv : env -> EcIdent.t -> form -> t

  val pp : env -> Format.formatter -> t -> unit
end

val s_write  : ?except_fs:EcPath.Sx.t -> env -> stmt -> PV.t
val is_write : ?except_fs:EcPath.Sx.t -> env -> PV.t -> instr list -> PV.t
val f_write  : ?except_fs:EcPath.Sx.t -> env -> EcPath.xpath -> PV.t

val e_read   : env -> PV.t -> expr -> PV.t
val s_read   : env -> stmt -> PV.t
val is_read  : env -> PV.t -> instr list -> PV.t 
val f_read   : env -> EcPath.xpath -> PV.t

exception EqObsInError

module Mpv2 : sig
  type t 
  val to_form : EcIdent.t -> EcIdent.t -> t -> form -> form
  val of_form : env -> EcIdent.t -> EcIdent.t -> form -> t
  val needed_eq : env -> EcIdent.t -> EcIdent.t -> form -> t
  val union   : t -> t -> t
  val subset   : t -> t -> bool
  val equal    : t -> t -> bool
  val remove : EcEnv.env -> EcTypes.prog_var -> EcTypes.prog_var -> t -> t
  (* remove_glob mp t, mp should be a top abstract functor *)
  val remove_glob : mpath -> t -> t
  val add_glob : EcEnv.env -> mpath -> mpath -> t -> t

  val check_glob : t -> unit 
end

val add_eqs : EcEnv.env -> Mpv2.t -> EcTypes.expr -> EcTypes.expr -> Mpv2.t

val eqobs_in :
  EcEnv.env ->
  ('log ->
   EcPath.xpath -> EcPath.xpath -> Mpv2.t -> 'log * Mpv2.t * 'spec) ->
  'log ->
  EcModules.stmt ->
  EcModules.stmt ->
  Mpv2.t ->
  PV.t * PV.t ->
  EcModules.stmt * EcModules.stmt * ('log * 'spec list) * Mpv2.t

val check_module_in : env -> mpath -> module_type -> unit
