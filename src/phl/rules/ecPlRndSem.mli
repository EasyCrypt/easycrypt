(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv

(* -------------------------------------------------------------------- *)
(* Semantic sampling of a straight-line statement, used by the [rndsem]
   program transformation ([EcTrRndSem]).

   [semrnd env me used s] — [s] must consist of assignments and samplings
   only, and write no global. Returns the single sampling

     wr <$ D(s)

   where [wr] are the program variables written by [s] (only those in [used],
   when given), in order of first write, and [D(s)] is the distribution of
   their final values: [s] read as nested [dlet] / [dunit]. When [wr] is
   empty, a fresh [unit] variable is bound in [me] and sampled instead; the
   (possibly extended) memory is returned with the instruction.

   Raises [InvalidSemRnd] when [s] is not of the expected form. *)
exception InvalidSemRnd

val semrnd :
  env -> memenv -> EcPV.PV.t option -> instr list -> memenv * instr list
