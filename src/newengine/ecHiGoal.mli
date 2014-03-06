(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal

(* -------------------------------------------------------------------- *)
type ttenv = {
  tt_engine  : ptactic_core -> FApi.backward;
  tt_provers : EcParsetree.pprover_infos -> EcProvers.prover_infos;
  tt_smtmode : [`Admit | `Strict | `Standard];
}

(* -------------------------------------------------------------------- *)
val process1_logic : ttenv -> logtactic -> FApi.backward
val process1_phl   : phltactic -> FApi.backward
