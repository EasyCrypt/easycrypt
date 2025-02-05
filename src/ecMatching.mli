(* -------------------------------------------------------------------- *)
open EcMaps
open EcUid
open EcIdent
open EcTypes
open EcModules
open EcFol
open EcUnify
open EcEnv
open EcGenRegexp

(* -------------------------------------------------------------------- *)
module Position : sig
  type cp_match = [
    | `If
    | `While
    | `Match
    | `Assign of lvmatch
    | `AssignTuple of lvmatch
    | `Sample of lvmatch
    | `Call   of lvmatch
  ]

  and lvmatch = [ `LvmNone | `LvmVar of EcTypes.prog_var ]

  type cp_base = [
    | `ByPos of int
    | `ByMatch of int option * cp_match
  ]

  type codepos_brsel = [`Cond of bool | `Match of EcSymbols.symbol]
  type codepos1      = int * cp_base
  type codepos       = (codepos1 * codepos_brsel) list * codepos1
  type codeoffset1   = [`ByOffset of int | `ByPosition of codepos1]

  val shift1 : offset:int -> codepos1 -> codepos1
  val shift  : offset:int -> codepos  -> codepos

  val resolve_offset : base:codepos1 -> offset:codeoffset1 -> codepos1
end

(* -------------------------------------------------------------------- *)
module Zipper : sig
  open Position

  type spath_match_ctxt = {
    locals : (EcIdent.t * ty) list;
    prebr  : ((EcIdent.t * ty) list * stmt) list;
    postbr : ((EcIdent.t * ty) list * stmt) list;
  }

  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath
  | ZMatch  of expr * spath * spath_match_ctxt

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
    z_env  : env option;                (* env with local vars from previous instructions *)
  }

  exception InvalidCPos

  (* Create a codepos1 from a top-level absolute position *)
  val cpos : int -> codepos1

  (* Split a statement from a top-level position (codepos1) *)
  val find_by_cpos1  : ?rev:bool -> env -> codepos1 -> stmt -> instr list * instr * instr list
  val split_at_cpos1 : env -> codepos1 -> stmt -> instr list * instr list

  (* Split a statement from an optional top-level position (codepos1) *)
  val may_split_at_cpos1 : ?rev:bool -> env -> codepos1 option -> stmt -> instr list * instr list

  (* Find the absolute offset of a top-level position (codepos1) w.r.t. a given statement *)
  val offset_of_position : env -> codepos1 -> stmt -> int

  (* [zipper] soft constructor *)
  val zipper : ?env : env -> instr list -> instr list -> ipath -> zipper

  (* Return the zipper for the stmt [stmt] at code position [codepos].
   * Raise [InvalidCPos] if [codepos] is not valid for [stmt]. It also
   * returns a input code-position, but fully resolved (i.e. with absolute
   * positions only). The second variant simply throw away the second
   * output.
   *)
  val zipper_of_cpos_r : env -> codepos -> stmt -> zipper * codepos
  val zipper_of_cpos : env -> codepos -> stmt -> zipper

  (* Zip the zipper, returning the corresponding statement *)
  val zip : zipper -> stmt

  (* [after ~strict zpr] returns all the statements that come after the
   * zipper cursor. They are returned as a list of statements, where the head
   * is the list of instructions coming directly after the cursor at the
   * same level, the next element is the ones coming after the cursor
   * parent block, and so forth. The cursor is included iff [strict] is [true].
   *)
  val after : strict:bool -> zipper -> instr list list

  type ('a, 'state) folder = env -> 'a -> 'state -> instr -> 'state * instr list
  type ('a, 'state) folder_tl = env -> 'a -> 'state -> instr -> instr list -> 'state * instr list

  (* [fold env v cpos f state s] create the zipper for [s] at [cpos], and apply
   * [f] to it, along with [v] and the state [state]. [f] must return the
   * new [state] and a new [zipper]. These last are directly returned.
   *
   * Raise [InvalidCPos] if [cpos] is not valid for [s], or any exception
   * raised by [f].
   *)
  val fold : env -> 'a -> codepos -> ('a, 'state) folder -> 'state -> stmt -> 'state * stmt

  (* Same as above but using [folder_tl]. *)
  val fold_tl : env -> 'a -> codepos -> ('a, 'state) folder_tl -> 'state -> stmt -> 'state * stmt

  (* [map cpos env f s] is a special case of [fold] where the state and the
   * out-of-band data are absent
   *)
  val map : env -> codepos -> (instr -> 'a * instr list) -> stmt -> 'a * stmt

end

(* -------------------------------------------------------------------- *)
(* Formulas rigid unification                                           *)
(* -------------------------------------------------------------------- *)
type 'a evmap

module EV : sig
  val empty     : 'a evmap
  val of_idents : ident list -> 'a evmap

  val add    : ident -> 'a evmap -> 'a evmap
  val mem    : ident -> 'a evmap -> bool
  val isset  : ident -> 'a evmap -> bool
  val set    : ident -> 'a -> 'a evmap -> 'a evmap
  val get    : ident -> 'a evmap -> [`Unset | `Set of 'a] option
  val doget  : ident -> 'a evmap -> 'a
  val fold   : (ident -> 'a -> 'b -> 'b) -> 'a evmap -> 'b -> 'b
  val filled : 'a evmap -> bool
end

(* -------------------------------------------------------------------- *)
type mevmap = {
  evm_form : form            evmap;
  evm_mem  : EcMemory.memory evmap;
  evm_mod  : EcPath.mpath    evmap;
}

(* -------------------------------------------------------------------- *)
module MEV : sig
  type item = [
    | `Form of form
    | `Mem  of EcMemory.memory
    | `Mod  of EcPath.mpath
  ]

  type kind = [ `Form | `Mem | `Mod ]

  val empty     : mevmap
  val of_idents : ident list -> kind -> mevmap

  val add    : ident -> kind -> mevmap -> mevmap
  val mem    : ident -> kind -> mevmap -> bool
  val isset  : ident -> kind -> mevmap -> bool
  val set    : ident -> item -> mevmap -> mevmap
  val get    : ident -> kind -> mevmap -> [`Unset | `Set of item] option
  val filled : mevmap -> bool
  val fold   : (ident -> item -> 'a -> 'a) -> mevmap -> 'a -> 'a
  val assubst: EcUnify.unienv -> mevmap -> env -> EcFol.f_subst
end

(* -------------------------------------------------------------------- *)
exception MatchFailure

type fmoptions = {
  fm_delta  : bool;
  fm_conv   : bool;
  fm_horder : bool;
}

val fmsearch   : fmoptions
val fmrigid    : fmoptions
val fmdelta    : fmoptions
val fmnotation : fmoptions

val f_match_core :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * mevmap
  -> form
  -> form
  -> unienv * mevmap

val f_match :
     fmoptions
  -> EcEnv.LDecl.hyps
  -> unienv * mevmap
  -> form
  -> form
  -> unienv * (ty Muid.t) * mevmap

(* -------------------------------------------------------------------- *)
type ptnpos = private [`Select of int | `Sub of ptnpos] Mint.t
type occ    = [`Inclusive | `Exclusive] * Sint.t

exception InvalidPosition
exception InvalidOccurence

module FPosition : sig
  type select = [`Accept of int | `Continue]

  val empty : ptnpos

  val is_empty : ptnpos -> bool

  val reroot : int list -> ptnpos -> ptnpos

  val tostring : ptnpos -> string

  val select : ?o:occ -> (Sid.t -> form -> select) -> form -> ptnpos

  val select_form : ?xconv:EcReduction.xconv -> ?keyed:bool ->
    LDecl.hyps -> occ option -> form -> form -> ptnpos

  val is_occurences_valid : Sint.t -> ptnpos -> bool

  val occurences : ptnpos -> int

  val filter : occ -> ptnpos -> ptnpos

  val map : ptnpos -> (form -> form) -> form -> form

  val topattern : ?x:EcIdent.t -> ptnpos -> form -> EcIdent.t * form
end

(* -------------------------------------------------------------------- *)
type cptenv = CPTEnv of f_subst

val can_concretize : mevmap -> EcUnify.unienv -> bool

(* -------------------------------------------------------------------------- *)
type regexp_instr = regexp1_instr gen_regexp

and regexp1_instr =
  | RAssign
  | RSample
  | RCall
  | RIf        of regexp_instr * regexp_instr
  | RWhile     of regexp_instr

module RegexpStmt : sig
  type regexp  = regexp_instr
  type subject = instr list
  type matches = subject Mstr.t

  val search : regexp -> subject -> matches option
end
