(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcParsetree
open EcEnv
open EcMemory
open EcModules
open EcFol

open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)

(* Please, note that WP only operates over assignments and conditional
 * statements.  Any weakening of this restriction may break the
 * soundness of the bounded hoare logic.
 *)

val wp : ?uselet:bool -> ?onesided:bool -> env -> memory -> stmt -> form -> instr list * form

val t_wp : ?uselet:bool -> (int doption) option -> backward
