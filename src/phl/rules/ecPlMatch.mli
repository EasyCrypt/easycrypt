(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Branches of a [match] instruction, instantiated on fresh program
   variables. Shared by the single-sided [match] rules of every logic. *)

type match_branch = {
  mb_mem  : memenv;   (* memory, extended with the fresh variables ys *)
  mb_cond : ss_inv;   (* e = C ys, in that memory *)
  mb_body : stmt;     (* the branch, its pattern variables replaced by ys *)
}

(* [match_branches env me e bs]: for [match e with | C_i xs_i => b_i end]
   in memory [me], one [match_branch] per constructor [C_i] of the type of
   [e], in declaration order. Each branch extends [me] with fresh program
   variables [ys_i], named after [xs_i] and of the same types (not in [me],
   hence not read by the judgement, nor written by [b_i]). *)
val match_branches :
  env -> memenv -> expr -> ((EcIdent.t * ty) list * stmt) list
  -> match_branch list
