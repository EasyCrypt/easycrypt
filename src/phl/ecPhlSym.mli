open EcBaseLogic
open EcLogic

(* -------------------------------------------------------------------- *)
(* Symmetry rule for equiv                                              *)

(*  
 *  c2 ~ c1 : fun m2 m1 -> P m1 m2 ==> fun m2 m1 -> Q m1 m2
 *  --------------------------------------------------------
 *      c1 ~ c2 : P ==> Q
 *)
class rn_equiv_sym : object
  inherit xrule
end

val t_equivS_sym : tactic
val t_equivF_sym : tactic
val t_equiv_sym  : tactic
val process_equiv_sym : tactic
