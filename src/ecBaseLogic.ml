(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
open EcTypes
open EcCoreFol

(* -------------------------------------------------------------------- *)
type local_kind =
| LD_var    of ty * form option
| LD_mem    of EcMemory.memtype
| LD_modty  of EcModules.module_type * EcModules.mod_restr
| LD_hyp    of form
| LD_abs_st of EcModules.abs_uses

type l_local = EcIdent.t * local_kind

type hyps = {
  h_tvar  : EcDecl.ty_params;
  h_local : l_local list;
}
