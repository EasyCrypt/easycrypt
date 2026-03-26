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

  exception InvalidCPos

  type cp_base = [
    | `ByPos of int (* Always <> 0 *)
    | `ByMatch of int option * cp_match
  ]

  (* Branch selection *)
  type codepos_brsel  = [`Cond of bool | `Match of EcSymbols.symbol]
  type nm_codepos_brsel = [`Cond of bool | `Match of int]

  (* Linear code position inside a block *)
  type codepos1 = int * cp_base

  (* Normalized code position inside a block, always > 0 *)
  type nm_codepos1 = int

  (* Codeposition path step *)
  type codepos_step    = (codepos1 * codepos_brsel)
  type nm_codepos_step = (int * nm_codepos_brsel)

  (* Block selection by codepos + branch selection *)
  type codepos_path    = codepos_step list
  type nm_codepos_path = nm_codepos_step list

  (* Full codeposition = path to block + position in block *)
  type codepos    = codepos_path * codepos1
  type nm_codepos = nm_codepos_path * nm_codepos1

  (* Code position offset *)
  type codeoffset1 = [`Relative of int | `Absolute of codepos1]

  (* Top-level first and last position *)
  val cpos_first : codepos
  val cpos_last  : codepos
  
  (* Block-level first and last position *)
  val cpos1_first       : codepos1
  val cpos1_last        : codepos1
  val cpos1_after_last  : codepos1

  val cpos1_to_top : codepos1 -> codepos

  val shift1 : offset:int -> codepos1 -> codepos1
  val shift  : offset:int -> codepos  -> codepos

  val resolve_offset : base:codepos1 -> offset:codeoffset1 -> codepos1

  module Notations : sig
    val (|+>) : codepos -> int -> codepos

    val (+>) : codepos1 -> int -> codepos1

    val (<+|) : codepos -> int -> codepos

    val (<+) : codepos1 -> int -> codepos1
  end

  (* Normalization functions *)
  val find_by_cp_match : env -> (int option * cp_match) -> stmt -> instr list * instr * instr list

  val exists_match : env -> cp_match -> stmt -> bool

  val find_by_nmcpos1 : ?rev:bool -> nm_codepos1 -> stmt -> instr list * instr * instr list

  val check_nm_cpos1 : nm_codepos1 -> stmt -> unit

  val normalize_cp_base : ?check:bool -> env -> cp_base -> stmt -> nm_codepos1

  val normalize_cpos1 : ?check:bool -> env -> codepos1 -> stmt -> nm_codepos1

  val resolve_offset1_from_cpos1 : env -> nm_codepos1 -> codeoffset1 -> stmt -> nm_codepos1 

  val find_by_cpos1 : ?rev:bool -> env -> codepos1 -> stmt -> instr list * instr * instr list

  val select_match_arm_idx : env -> expr -> string -> int

  val normalize_brsel : env -> instr -> codepos_brsel -> (env * stmt) * nm_codepos_brsel

  val select_branch : env -> instr -> codepos_brsel -> stmt

  val normalize_cpos_step : env -> stmt -> codepos_step -> (env * stmt) * nm_codepos_step

  val normalize_cpos_path : env -> codepos_path -> stmt -> (env * stmt) * nm_codepos_path

  val normalize_cpos : env ->  codepos -> stmt -> (env * stmt) * nm_codepos

  val cpos1 : int -> codepos1

  (* --- Gap types --- *)
  (* Normalized gap inside a block, 0-indexed, range [0, n] *)
  type nm_codegap1 = int

  (* Typed but unnormalized gap *)
  type codegap1 =
    | GapBefore of codepos1
    | GapAfter  of codepos1

    (* Full gap with path *)
  type codegap  = codepos_path * codegap1

  (* Normalized gap with path *)
  type nm_codegap = nm_codepos_path * nm_codegap1

  (* Gap-based ranges *)
  type codegap1_range = codegap1 * codegap1
  type nm_codegap1_range = nm_codegap1 * nm_codegap1
  type codegap_range  = codepos_path * codegap1_range
  type nm_codegap_range = nm_codepos_path * nm_codegap1_range

  (* Gap-based offset for swap *)
  type codegap_offset1 =
    | GapAbsolute of codegap1
    | GapRelative of int

  (* Boundary gap constructors *)
  val codegap1_start : codegap1
  val codegap1_end   : codegap1
  val codegap_start  : codegap
  val codegap_end    : codegap

  (* Convenience constructors *)
  val gap_before_pos   : codepos1 -> codegap1
  val gap_after_pos    : codepos1 -> codegap1
  val instr_before_gap : codegap1 -> codepos1
  val instr_after_gap  : codegap1 -> codepos1

  (* Code gap to anchored empty ranges *)
  val empty_codegap1_range_of_codegap1 : codegap1 -> codegap1_range
  val empty_codegap_range_of_codegap   : codegap  -> codegap_range

  (* Position <-> Gap conversions (normalized, 0-indexed) *)
  val gap_before    : nm_codepos1 -> nm_codegap1
  val gap_after     : nm_codepos1 -> nm_codegap1
  val instr_after   : nm_codegap1 -> nm_codepos1
  val instr_before  : nm_codegap1 -> nm_codepos1

  (* Single-instruction range as gap pair *)
  val gap_range_of_pos  : nm_codepos1 -> nm_codegap1_range
  val gap_range_of_cpos : nm_codepos  -> nm_codegap_range

  (* Gap counting helpers *)
  val gap_after_n       : int -> codegap1
  val gap_before_n      : int -> codegap1
  val gap_after_last_n  : int -> codegap1
  val gap_before_last_n : int -> codegap1

  (* Gap normalization *)
  val check_nm_cgap1        : nm_codegap1 -> stmt -> unit
  val normalize_cgap1       : env -> codegap1 -> stmt -> nm_codegap1
  val normalize_cgap        : env -> codegap  -> stmt -> (env * stmt) * nm_codegap
  val normalize_cgap1_range : env -> codegap1_range -> stmt -> nm_codegap1_range
  val normalize_cgap_range  : env -> codegap_range  -> stmt -> (env * stmt) * nm_codegap_range

  (* Split at gap *)
  val split_at_nmcgap1   : nm_codegap1 -> stmt -> instr list * instr list
  val split_at_cgap1     : env -> codegap1 -> stmt -> instr list * instr list
  val split_at_cgap      : env -> codegap  -> stmt -> env * (instr list * instr list)
  val may_split_at_cgap1 : ?rev:bool -> env -> codegap1 option -> stmt -> instr list * instr list

  (* Range operations on gaps *)
  val split_by_nmcgap_range : nm_codegap1_range -> stmt -> instr list * instr list * instr list
  val split_by_nmcgaps      : nm_codegap1 list -> stmt -> instr list list

  (* Resolve gap offset relative to a gap range *)
  val resolve_gap_offset : env -> nm_codegap1_range -> codegap_offset1 -> stmt -> nm_codegap1

  (* Semantic helpers for match-based finding *)
  val find_last_match  : env -> cp_match -> stmt -> instr list * instr * instr list
  val find_first_match : env -> cp_match -> stmt -> instr list * instr * instr list
  val find_nth_match   : env -> int -> cp_match -> stmt -> instr list * instr * instr list

  (* [split_by_match env ~occ ~gap cm s] splits [s] at the gap before/after
     the [occ]-th occurrence of [cm]. *)
  val split_by_match : env -> occ:int -> gap:[`Before | `After] -> cp_match -> stmt -> instr list * instr list

  val gap_before_match : env -> occ:int -> cp_match -> stmt -> nm_codegap1
  val gap_after_match  : env -> occ:int -> cp_match -> stmt -> nm_codegap1

  (* Block iteration *)
  val fold_blocks : start:nm_codegap1 -> block_size:int -> stmt ->
    (int -> nm_codegap1 -> nm_codegap1 -> 'a -> 'a) -> 'a -> 'a
  val iter_blocks : start:nm_codegap1 -> block_size:int -> stmt ->
    (int -> nm_codegap1 -> nm_codegap1 -> unit) -> unit

  (* Conversion between pos and gap for ranges *)
  val codegap1_range_of_codepos1 : codepos1 -> codegap1_range
  val codegap_range_of_codepos   : codepos  -> codegap_range

  val nm_codegap1_range_of_nm_codepos1 : nm_codepos1 -> nm_codegap1_range
  val nm_codegap_range_of_nm_codepos   : nm_codepos  -> nm_codegap_range

  val disjoint : nm_codegap1_range -> nm_codegap1_range -> bool

  val nm_codepos1_in_nm_codegap1_range : nm_codepos1 -> nm_codegap1_range -> bool
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

  (* Find the absolute offset of a top-level position (codepos1) w.r.t. a given statement *)
(*   val offset_of_position : env -> codepos1 -> stmt -> int *)

  (* [zipper] soft constructor *)
  val zipper : ?env : env -> instr list -> instr list -> ipath -> zipper

  (* Return the zipper for the stmt [stmt] at code position [codepos].
   * Raise [InvalidCPos] if [codepos] is not valid for [stmt]. It also
   * returns a input code-position, but fully resolved (i.e. with absolute
   * positions only). The second variant simply throw away the second
   * output.
   *)
  val zipper_of_cpos_r : env -> codepos -> stmt -> zipper * (nm_codepos * stmt)
  val zipper_of_cpos : env -> codepos -> stmt -> zipper

  (* Return the zipper for the stmt [stmt] from the start of the code position
   * range [codepos_range]. It also returns a code position relative to
   * the zipper that represents the final position in the range.
   * Raise [InvalidCPos] if [codepos_range] is not a valid range for [stmt].
   *)
(*   val zipper_of_cpos_range : env -> codepos_range -> stmt -> zipper * codepos1 *)
  val zipper_and_split_of_cgap_range : env -> codegap_range -> stmt -> zipper * (instr list * instr list * instr list) * nm_codegap_range

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
  type ('a, 'state) folder_l = env -> 'a -> 'state -> instr list -> 'state * instr list

  (* [fold env v cpos f state s] create the zipper for [s] at [cpos], and apply
   * [f] to it, along with [v] and the state [state]. [f] must return the
   * new [state] and a new [zipper]. These last are directly returned.
   *
   * Raise [InvalidCPos] if [cpos] is not valid for [s], or any exception
   * raised by [f].
   *)
  val fold : env -> 'a -> codepos -> ('a, 'state) folder -> 'state -> stmt -> 'state * stmt

  (* [map cpos env f s] is a special case of [fold] where the state and the
   * out-of-band data are absent
   *)
  val map : env -> codepos -> (instr -> 'a * instr list) -> stmt -> 'a * stmt

  (* Variants of the above but using code position ranges *)
  val fold_range : env -> 'a -> codegap_range -> ('a, 'state) folder_l -> 'state -> stmt -> 'state * stmt
  val map_range : env -> codegap_range -> (env -> instr list -> instr list) -> stmt -> stmt


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
