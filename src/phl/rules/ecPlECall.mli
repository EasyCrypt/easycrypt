(* -------------------------------------------------------------------- *)
open EcAst
open EcEnv
open EcCoreGoal

(* -------------------------------------------------------------------- *)
(* Elaboration shared by the [ecall] tactics of every logic
   ([Ec<Logic>ECall]): a call whose specification is given as a proof
   term (the contract), whose program variables are abstracted. *)

type call = EcModules.lvalue option * EcPath.xpath * EcTypes.expr list

type calls = [
  | `Single of call
  | `Double of call * call
]

(* [process_contract pe penv hyps (c, tvi, args)] types the contract [c]
   applied to [args] in [penv] (the hypotheses with the memories of the
   goal), applies it to as many holes as possible in [hyps], and returns
   it as a proof term and its conclusion. *)
val process_contract :
  proofenv -> LDecl.hyps -> LDecl.hyps -> EcParsetree.pecall
  -> proofterm * form

(* [check_contract_type ?loc ?phoare ?noexn ~name pe hyps calls ctt]
   checks that [ctt] (after a head reduction) is a specification of the
   called procedure(s): [hoare [f : _ ==> _]] (with no exceptional
   postcondition when [noexn], the default), or [phoare [f : _ ==> _]] if
   [phoare], for a [`Single] call; [equiv [fL ~ fR : _ ==> _]] for a
   [`Double] call. Fails with a user-facing error otherwise. *)
val check_contract_type :
     ?loc:EcLocation.t
  -> ?phoare:bool
  -> ?noexn:bool
  -> name:EcSymbols.qsymbol
  -> proofenv
  -> LDecl.hyps
  -> calls
  -> form
  -> unit

(* [abstract_pvs hyps ms pvs] is [(ids, fs, s)]: for each memory of
   [ms], in order, each program variable [x] of [pvs] in that memory is
   given a fresh local [x_] (typed, in [ids]); [fs] are the program
   variables as formulas, [s] the substitution of the program variables by
   their locals. *)
val abstract_pvs :
     LDecl.hyps
  -> memory list
  -> ((prog_var * ty) list) EcIdent.Mid.t
  -> (EcIdent.t * ty) list * form list * EcPV.PVM.subst

(* [restore_pvs ids fs] substitutes back the program variables [fs] for
   their locals [ids]. *)
val restore_pvs : (EcIdent.t * ty) list -> form list -> EcSubst.subst

(* [subst_pt_args env s pt] applies the substitution [s] of program
   variables to the arguments of the proof term [pt] (an application). *)
val subst_pt_args : env -> EcPV.PVM.subst -> proofterm -> proofterm
