(* -------------------------------------------------------------------- *)
open EcParsetree
open EcCoreGoal.FApi
open EcAst

(* ==================================================================== *)
(* Rules (trusted)                                                      *)

type equiv_pr = {
  epr_ty    : ty;       (* the common type t of phi_l and phi_r *)
  epr_left  : ss_inv;   (* phi_l, in the left final memory *)
  epr_right : ss_inv;   (* phi_r, in the right final memory *)
}

(* [t_equivF_pr { epr_ty = t; epr_left = phi_l; epr_right = phi_r }] — an
   equivalence of two procedures, reduced to the equality of the
   distributions of [phi_l] and [phi_r]:

     forall &1 &2, forall (a : t), phi_l = a => phi_r = a => Q
     forall &1 &2, forall (a : t),
        P => Pr[f1(args1) @ &1 : phi_l = a] = Pr[f2(args2) @ &2 : phi_r = a]
     --------------------------------------------------------------------
                       equiv [f1 ~ f2 : P ==> Q]

   where [args1] (resp. [args2]) are the arguments of [f1] (resp. [f2])
   read in [&1] (resp. [&2]); in the first premise, [&1] and [&2] are the
   final memories. Side condition: [phi_l] and [phi_r] have type [t]
   (otherwise fails).

   Node: [REquivFPr { epr_ty = t; epr_left = phi_l; epr_right = phi_r }].
   Checker: "equivF-pr". *)
val t_equivF_pr : equiv_pr -> backward

(* ==================================================================== *)
(* Elaboration                                                          *)

(* [bypr phi_l phi_r] on an [equivF] goal: [phi_l] (resp. [phi_r]) is
   typed in the left (resp. right) final memory, and their types must be
   convertible. Applies [t_equivF_pr]. *)
val process_equivF_pr : pformula * pformula -> backward
