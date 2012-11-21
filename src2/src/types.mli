(* -------------------------------------------------------------------- *)
type tybase = Tunit | Tbool | Tint | Treal

type ty =
  | Tbase   of tybase
  | Tvar    of UidGen.uid
  | Tunivar of UidGen.uid
  | Trel    of int
  | Ttuple  of ty list
  | Tconstr of Path.path * ty list

(* -------------------------------------------------------------------- *)
val tunit : unit -> ty
val tbool : unit -> ty
val tint  : unit -> ty

val mkunivar : unit -> ty
