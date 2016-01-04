(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcPath
open EcFol
open EcEnv
open EcProvers

(* -------------------------------------------------------------------- *)
val check : ?notify:notify -> prover_infos -> LDecl.hyps -> form -> bool
val dump_why3 : env -> string -> unit

module Frequency : sig

  (* -------------------------------------------------------------------- *)
  type relevant = Sp.t * Sx.t

  val r_empty : relevant
  val r_inter : relevant -> relevant -> relevant
  val r_diff  : relevant -> relevant -> relevant
  val r_card  : relevant -> int

  type all_rel = [ `OP of path | `PROC of xpath]

  val r_fold : (all_rel -> 'a -> 'a) -> relevant -> 'a -> 'a

  type frequency

  val create : Sp.t -> frequency
  val frequency : frequency -> all_rel -> int
  val f_ops : Sp.t -> form -> relevant

  val add : frequency -> EcDecl.axiom -> unit

end



