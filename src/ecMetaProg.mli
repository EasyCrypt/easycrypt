(* -------------------------------------------------------------------- *)
(* Expressions / formulas matching for tactics                          *)
(* -------------------------------------------------------------------- *)

open EcIdent
open EcTypes
open EcModules

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
