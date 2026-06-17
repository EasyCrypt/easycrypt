(* Smoke instantiation of the Rényi-∞ oracle theories.

   Realizes every parameter axiom of [RDivOracle] and [RDivOracleValid]
   at a trivial instance (unit parameter, identical kernels, M = 1),
   checking that the two axiom sets are jointly satisfiable — i.e. that
   the abstract theories cannot be used to derive an inconsistency. *)

require import AllCore Distr RDivOracle.

clone RDivOracle as Triv with
  type out_t   <- bool,
  type param_t <- unit,
  op d_param   <- dunit tt,
  op d1        <- fun (_ : unit) => dunit true,
  op d2        <- fun (_ : unit) => dunit true,
  op N         <- 1,
  op M         <- 1%r
  proof *.
realize d_param_ll by exact dunit_ll.
realize d1_ll by move => *; exact dunit_ll.
realize d2_ll by move => *; exact dunit_ll.
realize N_ge0 by trivial.
realize M_ge0 by trivial.
realize d1_dominated_d2 by move => *; smt().

clone RDivOracleValid as TrivV with
  type out_t   <- bool,
  type param_t <- unit,
  op d_full    <- dunit tt,
  op valid     <- predT,
  op d1        <- fun (_ : unit) => dunit true,
  op d2        <- fun (_ : unit) => dunit true,
  op N         <- 1,
  op M         <- 1%r
  proof *.
realize d_full_ll by exact dunit_ll.
realize d1_ll by move => *; exact dunit_ll.
realize d2_ll by move => *; exact dunit_ll.
realize N_ge0 by trivial.
realize M_ge0 by trivial.
realize d1_dominated_d2 by move => *; smt().
realize valid_nondegenerate by smt(dunit_ll).
