(* -------------------------------------------------------------------- *)
open EcParsetree
open EcIdent
open EcTypes
open EcModules

(* -------------------------------------------------------------------- *)
module Zipper : sig
  type ipath =
  | ZTop
  | ZWhile  of expr * spath
  | ZIfThen of expr * spath * stmt
  | ZIfElse of expr * stmt  * spath

  and spath = (instr list * instr list) * ipath

  type zipper = {
    z_head : instr list;                (* instructions on my left (rev)       *)
    z_tail : instr list;                (* instructions on my right (me incl.) *)
    z_path : ipath ;                    (* path (zipper) leading to me         *)
  }

  exception InvalidCPos

  val zipper : instr list -> instr list -> ipath -> zipper

  val zipper_of_cpos : codepos -> stmt -> zipper

  val zip : zipper -> stmt

  type ('a, 'state) folder =
    'a -> 'state -> instr -> 'state * instr list

  val fold : 'a -> codepos -> ('a, 'state) folder -> 'state -> stmt -> 'state * stmt
end

(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)
module IMatch : sig
  (* pattern can be
   * - b         => match single instruction with b, see below
   * - [b1...bn] => match one of b1 ... bn
   * - p*        => repeat p
   * - p+        => repeat p, at least 1 time
   * - p{n}      => match p `n' times
   * - (p)       => pattern grouping, for back-reference
   *
   * instruction pattern can be
   * - _ => any
   * - i => if-then-else
   * - w => while-loop
   *)

  type t
  type mtch

  exception InvalidPattern of string

  val compile : string -> t
  val match_  : t -> instr list -> mtch option

  val get : mtch -> int -> instr list

  val get_as_while : mtch -> int -> instr * (expr * stmt)
  val get_as_if    : mtch -> int -> instr * (expr * stmt * stmt)
end
