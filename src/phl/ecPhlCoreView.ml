(* -------------------------------------------------------------------- *)
(* The views between hoare and probability-0 bdhoare judgements live in
   [rules/hoare/ecHoareOfBdHoare] (a hoare goal from a bdhoare premise)
   and [rules/bdhoare/ecBdHoareOfHoare] (a bdhoare goal from a hoare
   premise). This module only keeps the legacy entry points, named after
   the goal they turn into: [t_hoare_of_bdhoare*] acts on a bdhoare goal. *)
let t_hoare_of_bdhoareS = EcBdHoareOfHoare.t_bdhoareS_of_hoare
let t_hoare_of_bdhoareF = EcBdHoareOfHoare.t_bdhoareF_of_hoare
let t_bdhoare_of_hoareS = EcHoareOfBdHoare.t_hoareS_of_bdhoare
let t_bdhoare_of_hoareF = EcHoareOfBdHoare.t_hoareF_of_bdhoare
