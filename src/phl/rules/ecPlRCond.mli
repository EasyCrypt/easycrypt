(* -------------------------------------------------------------------- *)
open EcSymbols
open EcAst
open EcEnv
open EcMatching.Position

(* -------------------------------------------------------------------- *)
(* Deciding a conditional ([if] / [while]) or a [match] at a given position
   of a statement, shared by the [rcond] and [rmatch] transformations
   ([EcTrRCond], [EcTrRMatch]), by the framed [rmatch] rules
   ([Ec<Logic>RMatch]) and by the tactics using them.

   The statement is [c = hd; i; tl], where [i = c[k]] is the instruction at
   the resolved index [k] and [hd = c[0..k)]. The computations are pure:
   positions are resolved indices, so the statement is never searched; they
   raise [EcPlTransform.InvalidTransform] when [i] is not of the expected
   form. *)

(* -------------------------------------------------------------------- *)
(* [rcond_select m k b c] decides the conditional [i] in favour of the
   branch [b]. Returns [(hd, g, c')] where, in memory [m]:

     i                     b      g     c'
     if e then s1 else s2  true   e     hd; s1; tl
     if e then s1 else s2  false  !e    hd; s2; tl
     while e do s1         true   e     hd; s1; while e do s1; tl
     while e do s1         false  !e    hd; tl

   Fails with "the targetted instruction is not a conditionnal" if [i] is
   neither an [if] nor a [while]. *)
val rcond_select : memory -> nm_codepos1 -> bool -> stmt -> stmt * ss_inv * stmt

(* -------------------------------------------------------------------- *)
(* The decomposition of [c] at [i = match e with ... | C xs => b | ...],
   decided in favour of its [j]-th constructor [C]: *)
type rmatch = {
  rm_hd       : stmt;     (* hd *)
  rm_post     : ss_inv;   (* exists xs, e = C xs   (in the memory of [c]) *)
  rm_me       : memenv;   (* the memory of [c], extended with fresh program
                             variables [ys] for [xs] *)
  rm_eq       : ss_inv;   (* e = C ys              (framed form) *)
  rm_framed   : stmt;     (* hd; b[ys/xs]; tl      (framed form) *)
  rm_unframed : stmt;     (* hd; ys <- oget (get_as_C e); b[ys/xs]; tl
                             (no assignment when [C] has no argument) *)
}

(* [rmatch_select env me k j c]: the decomposition above, [me] being the
   memory of [c]. Fails with "the targetted instruction is not a match" if
   [i] is not a [match], or "invalid constructor index" if it has no
   [j]-th branch. *)
val rmatch_select : env -> memenv -> nm_codepos1 -> int -> stmt -> rmatch

(* [rmatch_can_frame env ~can_frame k c]: whether the framed form of
   [rmatch] applies to the [match] [i] (false if [i] is not a [match]):
   the variables read by [e] are neither read nor written by [hd] (so that
   [e] has the same value before and after [hd]), and [can_frame] holds or
   [hd] is empty. [can_frame] is given by the logic: the framed form is
   only sound for judgements that ignore the initial memories in which
   [hd] does not terminate (see [Ec<Logic>RMatch]). *)
val rmatch_can_frame : env -> can_frame:bool -> nm_codepos1 -> stmt -> bool

(* -------------------------------------------------------------------- *)
(* Resolution, tactic side (never used by the rules or their checkers):
   resolve the position [k] in [c] and check the instruction, with the
   user-facing error messages, in this order: invalid position
   ([EcLowPhlGoal.InvalidSplit]), then the instruction is not of the
   expected form, then (rmatch) no constructor named [C]. *)

(* [resolve_rcond pe env k c]: the index of the conditional at [k]. *)
val resolve_rcond :
  EcCoreGoal.proofenv -> env -> codepos1 -> stmt -> nm_codepos1

(* [resolve_rmatch pe env k C c]: the index of the [match] at [k], and the
   index of [C] among the constructors of its datatype. *)
val resolve_rmatch :
  EcCoreGoal.proofenv -> env -> codepos1 -> symbol -> stmt -> nm_codepos1 * int
