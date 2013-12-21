(* -------------------------------------------------------------------- *)
open EcLogic

(* -------------------------------------------------------------------- *)
let t_trivial = 
  let subtc = 
    t_lor [EcPhlTauto.t_hoare_true;
           EcPhlTauto.t_core_exfalso;
           EcPhlPr.t_prbounded false;
           EcPhlSkip.t_skip]
  in
    t_try
      (t_lseq [t_try t_assumption;
               t_progress (t_id None);
               t_try t_assumption; 
               subtc; t_logic_trivial; t_fail])
