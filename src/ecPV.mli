(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcMaps
open EcPath
open EcTypes
open EcModules
open EcMemory
open EcEnv
open EcFol

(* -------------------------------------------------------------------- *)
type alias_clash =
 | AC_concrete_abstract of mpath * prog_var
 | AC_abstract_abstract of mpath * mpath

exception AliasClash of env * alias_clash

(* -------------------------------------------------------------------- *)
module Mnpv : Map.S with type key = prog_var
module Snpv : Set.S with module M = Map.MakeBase(Mnpv)

(* -------------------------------------------------------------------- *)
module PVMap : sig
  type 'a t

  val create : env -> 'a t
  val add    : prog_var -> 'a -> 'a t -> 'a t
  val find   : prog_var -> 'a t -> 'a option
  val raw    : 'a t -> 'a Mnpv.t
end

(* -------------------------------------------------------------------- *)
module Mpv : sig
  type ('a,'b) t

  val empty : ('a,'b) t

  val check_npv_mp : env -> prog_var -> mpath -> EcEnv.use -> unit

  val check_mp_mp : env -> mpath -> EcEnv.use -> mpath -> EcEnv.use -> unit

  val check_npv : env -> prog_var -> ('a,'b) t -> unit

  val check_glob : env -> mpath -> ('a,'b) t -> unit

  val add : env -> prog_var -> 'a -> ('a,'b) t -> ('a,'b) t

  val add_glob : env -> mpath -> 'b -> ('a,'b) t -> ('a,'b) t

  val find : env -> prog_var -> ('a,'b) t -> 'a

  val find_glob : env -> mpath -> ('a,'b) t -> 'b

  val issubst : env -> (expr, unit) t -> instr list -> instr list
end

(* -------------------------------------------------------------------- *)
exception MemoryClash

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

  val pick : t -> [`Global of mpath | `PV of prog_var] option

  val add      : env -> prog_var -> ty -> t -> t
  val add_glob : env -> mpath -> t -> t
  val remove   : env -> prog_var -> t -> t
  val union    : t -> t -> t
  val diff     : t -> t -> t
  val subset   : t -> t -> bool

  val interdep     : env -> t -> t -> t
  val indep        : env -> t -> t -> bool
  val check_depend : env -> t -> mpath -> unit
  val elements     : t -> (prog_var * ty) list * mpath list
  val ntr_elements : t -> (prog_var * ty) list * mpath list

  val mem_pv   : env -> prog_var -> t -> bool
  val mem_glob : env -> mpath -> t -> bool

  val fv : env -> EcIdent.t -> form -> t

  val pp : env -> Format.formatter -> t -> unit

  val iter : (prog_var -> ty -> unit) -> (mpath -> unit) -> t -> unit

  val check_notmod : EcEnv.env -> EcTypes.prog_var -> t -> bool
end

(* -------------------------------------------------------------------- *)
type 'a pvaccess = env -> PV.t -> 'a -> PV.t

val lp_write_r :                 lvalue     pvaccess
val i_write_r  : ?except:Sx.t -> instr      pvaccess
val is_write_r : ?except:Sx.t -> instr list pvaccess
val s_write_r  : ?except:Sx.t -> stmt       pvaccess
val f_write_r  : ?except:Sx.t -> xpath      pvaccess

val e_read_r   : expr       pvaccess
val i_read_r   : instr      pvaccess
val is_read_r  : instr list pvaccess
val s_read_r   : stmt       pvaccess
val f_read_r   : xpath      pvaccess

(* -------------------------------------------------------------------- *)
type 'a pvaccess0 = env -> 'a -> PV.t

val i_write  : ?except:Sx.t -> instr      pvaccess0
val is_write : ?except:Sx.t -> instr list pvaccess0
val s_write  : ?except:Sx.t -> stmt       pvaccess0
val f_write  : ?except:Sx.t -> xpath      pvaccess0

val e_read  : expr       pvaccess0
val i_read  : instr      pvaccess0
val is_read : instr list pvaccess0
val s_read  : stmt       pvaccess0
val f_read  : xpath      pvaccess0

(* -------------------------------------------------------------------- *)
exception EqObsInError

module Mpv2 : sig
  type t
  val to_form : EcIdent.t -> EcIdent.t -> t -> form -> form
  val of_form : env -> EcIdent.t -> EcIdent.t -> form -> t
  val needed_eq : env -> EcIdent.t -> EcIdent.t -> form -> t
  val union   : t -> t -> t
  val subset   : t -> t -> bool
  val equal    : t -> t -> bool
  val remove : env -> prog_var -> prog_var -> t -> t
  (* remove_glob mp t, mp should be a top abstract functor *)
  val remove_glob : mpath -> t -> t
  val add_glob : env -> mpath -> mpath -> t -> t
  val add_eqs : env -> expr -> expr -> t -> t
  val subst_l : env -> prog_var -> prog_var -> t -> t
  val subst_r : env -> prog_var -> prog_var -> t -> t
  val substs_l : env -> (prog_var * 'a) list -> prog_var list -> t -> t
  val substs_r : env -> (prog_var * 'a) list -> prog_var list -> t -> t

  val check_glob : t -> unit

  (* [mem x1 x2 eq] return true if (x1,x2) is in eq.
     x1 and x2 are assumed in normal form *)
  val mem : prog_var -> prog_var -> t -> bool
  val mem_glob : mpath -> t -> bool

  (* [iter fpv fabs eq] iterate fpv and fabs on all pair contained in eq.
     The argument given to both function are in normal form *)
  val iter :
    (prog_var -> prog_var -> ty -> unit) -> (mpath -> unit) -> t -> unit

  val eq_refl : PV.t -> t
  val fv2 : t -> PV.t
  val eq_fv2 : t -> t

  val split_nmod : env -> PV.t -> PV.t -> t -> t
  val split_mod : env -> PV.t -> PV.t -> t -> t

  val mem_pv_l : env -> prog_var -> t -> bool
  val mem_pv_r : env -> prog_var -> t -> bool
end

(* -------------------------------------------------------------------- *)
val i_eqobs_in_refl : env -> instr -> PV.t -> PV.t
val eqobs_inF_refl  : env -> EcPath.xpath -> PV.t -> PV.t
val check_module_in : env -> mpath -> module_type -> unit
