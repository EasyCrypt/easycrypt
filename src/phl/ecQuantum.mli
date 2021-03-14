exception NotWfQuantum of EcEnv.env * EcFol.form
exception NotClassical of EcEnv.env * EcFol.form

val check_wf_quantum : EcEnv.env -> EcFol.form -> unit
val check_classical  : EcEnv.env -> EcFol.form -> unit
