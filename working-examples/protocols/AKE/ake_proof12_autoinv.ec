include "ake_game2.ec".

timeout 10.

lemma asd :
forall 
 ( b1 : bool
 , complete_sessions1 : complete_session_with_status
 , incomplete_sessions1 : incomplete_session_with_status
 , corrupt1  : (part, bool) map
 , pkey1     : (part, public_key) map
 , skey1     : (part, secret_key) map
 , LH1       : (session_string, session_key) map
 , LHT1     : (session_string, session_key) map
 , seed1     : (message * part, eph_key) map
 , G1 : (session_id, session_key) map
 , tested_session1 : (session_id, session_key) map
 , b2 : bool
 , complete_sessions2 : complete_session_with_status
 , incomplete_sessions2 : incomplete_session_with_status
 , corrupt2  : (part, bool) map
 , pkey2     : (part, public_key) map
 , skey2     : (part, secret_key) map
 , LH2       : (session_string, session_key) map
 , LHT2     : (session_string, session_key) map
 , seed2     : (message * part, eph_key) map
 , G2 : (session_id, session_key) map
 , tested_session2 : (session_id, session_key) map
 , s1 : session_id
 , s2 : session_id),

 (invariant1(LH1,LH2) &&
 invariant2(G2, LH1, skey2, seed2) &&
 invariant3(G2,LH1, LH2, skey2, seed2) &&
 invariant5(seed1,skey1) &&
 (b1 = b2  && complete_sessions1 = complete_sessions2 &&
  incomplete_sessions1 = incomplete_sessions2 && 
  corrupt1 = corrupt2 && pkey1 = pkey2 && skey1 = skey2 && 
  seed1 = seed2 && LHT1 = LHT2 && tested_session1 = tested_session2 && s1 = s2))=>
(
(
forall (l:session_string),

!(!in_dom (l,LH2) && findelse_g_abs (G2,l,skey2,seed2) = None && 
                            in_dom (l,LH1))
)
&&
(forall (l:session_string),

(let findr_R = findelse_g_abs (G2,l,skey2,seed2) in
!in_dom (l,LH2) =>
findr_R <> None =>
in_dom (l,LH1) => LH1[l] = G2[proj (findr_R)])
)
&&
(
forall (l:session_string),
!(!in_dom (l,LH2) && findelse_g_abs (G2,l,skey2,seed2) <> None && !
                            in_dom (l,LH1))
)
&&
(
forall (l:session_string),
in_dom (l,LH2) =>
in_dom (l,LH1) => LH1[l] = LH2[l]
)
&&
(
forall (l:session_string),
!(in_dom (l,LH2) && !in_dom (l,LH1))
)
&&
 (b1 = b2  && complete_sessions1 = complete_sessions2 &&
  incomplete_sessions1 = incomplete_sessions2 && 
  corrupt1 = corrupt2 && pkey1 = pkey2 && skey1 = skey2 && 
  seed1 = seed2 && LHT1 = LHT2 && tested_session1 = tested_session2 && s1 = s2)).

equiv INV_KR : AKE.KeyReveal ~ AKE1.KeyReveal :
(
forall (l:session_string),

!(!in_dom (l,LH{2}) && findelse_g_abs (G{2},l,skey{2},seed{2}) = None && 
                            in_dom (l,LH{1}))
)
&&
(forall (l:session_string),

(let findr_R = findelse_g_abs (G{2},l,skey{2},seed{2}) in
!in_dom (l,LH{2}) =>
findr_R <> None =>
in_dom (l,LH{1}) => LH{1}[l] = G{2}[proj (findr_R)])
)
&&
(
forall (l:session_string),
!(!in_dom (l,LH{2}) && findelse_g_abs (G{2},l,skey{2},seed{2}) <> None && !
                            in_dom (l,LH{1}))
)
&&
(
forall (l:session_string),
in_dom (l,LH{2}) =>
in_dom (l,LH{1}) => LH{1}[l] = LH{2}[l]
)
&&
(
forall (l:session_string),
!(in_dom (l,LH{2}) && !in_dom (l,LH{1}))
)
&&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session,s} 
==>
(
forall (l:session_string),
!(!in_dom (l,LH{2}) && findelse_g_abs (G{2},l,skey{2},seed{2}) = None && 
                            in_dom (l,LH{1}))
)
&&
(
forall (l:session_string),
(let findr_R = findelse_g_abs (G{2},l,skey{2},seed{2}) in
!in_dom (l,LH{2}) =>
findr_R <> None =>
in_dom (l,LH{1}) => LH{1}[l] = G{2}[proj (findr_R)])
)
&&
(
forall (l:session_string),
!(!in_dom (l,LH{2}) && findelse_g_abs (G{2},l,skey{2},seed{2}) <> None && !
                            in_dom (l,LH{1}))
)
&&
(
forall (l:session_string),
in_dom (l,LH{2}) =>
in_dom (l,LH{1}) => LH{1}[l] = LH{2}[l]
)
&&
(
forall (l:session_string),
!(in_dom (l,LH{2}) && !in_dom (l,LH{1}))
)
&&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session,res} by auto. 

(*
equiv INV_KR : AKE.KeyReveal ~ AKE1.KeyReveal :
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session,s}) ==>
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}).
inline;derandomize;wp;rnd.
expand invariant1,invariant2,invariant3,invariant5.
trivial.
save.

equiv INV_T : AKE.Test ~ AKE1.Test :
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session,s}) ==>
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}).
inline;derandomize;wp;rnd.
expand invariant1,invariant2,invariant3,invariant5.
trivial.

equiv Fact1 : AKE.Main ~ AKE1.Main : true ==> ={ res }
 by
auto
(invariant1(LH{1}, LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2}, LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1}, skey{1}) &&
 LHT{1} = empty_map  &&
( ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session })).

claim Pr1 : AKE.Main[res] = AKE1.Main[res] using Fact1.


(* //KG, Init, Respond, Complete, Corrupt, KeyReveal, H, Test, EphKeyReveal *)
(*
prover vampire, z3, "alt-ergo", yices, cvc3, gappa.

equiv INV_KG : AKE.KG ~ AKE1.KG :
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session}) ==>
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
 ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}) by auto.

equiv INV_Init : AKE.Init ~ AKE1.Init :
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map  &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, A, B }) ==>
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2},LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{1},skey{1}) &&
  LHT{1} = empty_map &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}) by auto.

equiv INV_Respond : AKE.Respond ~ AKE1.Respond :
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map  &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, A, B, X }) ==>
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map  &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}) by auto.

equiv INV_Complete : AKE.Complete ~ AKE1.Complete :
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map &&
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, A, B, X, Y}) ==>
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map  &&
  ={b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, tested_session, seed, LHT }) by auto.

equiv INV_Corrupt : AKE.Corrupt ~ AKE1.Corrupt :
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, A, tested_session }) ==>
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, tested_session, LHT, res}) by auto.
*)



(* equiv INV_H : AKE.H ~ AKE1.H : *)
(*   (invariant1(LH{1},LH{2}) && *)
(*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) && *)
(*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) && *)
(*   invariant5(seed{2},skey{2}) && *)
(*   LHT{1} = empty_map && *)
(*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, lam, tested_session }) ==> *)
(*   (invariant1(LH{1},LH{2}) && *)
(*   invariant2(G{2}, LH{1}, skey{2}, seed{2}) && *)
(*   invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) && *)
(*   invariant5(seed{2},skey{2}) && *)
(*   LHT{1} = empty_map && *)
(*   ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}) by auto. *)
(* (\* wp. *\) *)
(* (\* rnd. *\) *)
(* (\* trivial. *\) *)
(* (\* save. *\) *)




(*
equiv INV_EphKeyReveal : AKE.EphKeyReveal ~ AKE1.EphKeyReveal :
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, A, X, tested_session }) ==>
  (invariant1(LH{1},LH{2}) &&
  invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
  invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
  invariant5(seed{2},skey{2}) &&
  LHT{1} = empty_map &&
  ={ b, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed, LHT, tested_session, res}) by auto.
wp.
trivial.

save.
*)
*)



