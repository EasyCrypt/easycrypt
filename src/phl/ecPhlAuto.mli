(* -------------------------------------------------------------------- *)
open EcSymbols
open EcCoreGoal.FApi

(* -------------------------------------------------------------------- *)
val t_exfalso     : backward
val t_phl_trivial : backward
val t_pl_trivial  : ?conv:[`Alpha | `Conv] -> ?bases:symbol list -> backward
val t_auto        : ?conv:[`Alpha | `Conv] -> backward
