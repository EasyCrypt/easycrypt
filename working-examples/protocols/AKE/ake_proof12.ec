include "ake_game2.ec".


pred invariant1 (LH1: (session_string, session_key) map, 
                 LH2: (session_string, session_key) map) =
forall (str : session_string),
 in_dom(str,LH2)  =>  (in_dom(str,LH1) && LH1[str] = LH2[str]).


pred invariant2 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map,
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map) =
forall (str : session_string, fer_sid : session_id),
(( findelse_g_abs(G2,str,skey2, seed2) <> None)
=> ( in_dom(str,LH1) &&  LH1[str] = G2[proj(findelse_g_abs(G2,str,skey2, seed2))] )).


pred  invariant3 (G2 : (session_id, session_key) map, 
                 LH1: (session_string, session_key) map, 
		 LH2: (session_string, session_key) map, 
                 skey2 : (part, secret_key ) map,
                 seed2 : (message * part, eph_key ) map ) =
forall (str : session_string), 
in_dom(str,LH1) => ( in_dom(str, LH2)  || findelse_g_abs(G2,str,skey2, seed2) <> None).

equiv INV12_KR : AKE.KeyReveal ~ AKE1.KeyReveal :
 (invariant1(LH{1},LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2},LH{1}, LH{2}, skey{2}, seed{2}) &&
 ={b, bad, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed,
  LHT, tested_session}).
sp 14 22.
rnd >>.
sp 1 3.
(*app 1 1 (sestr{2} = dummy_string &&
        sidB{2} = dummy_sid &&
         sidA{2} = dummy_sid &&
          sid{2} = dummy_sid &&
           ofeh{2} = None &&
            fer{2} = None &&
             matchb{2} = false &&
              ssskey{2} = dummy_session_key &&
               sstr{2} = dummy_string &&
                X'{2} = dummy_msg &&
                 A'{2} = dummy_part &&
                  eph_flagB{2} = false &&
                   eph_flagA{2} = false &&
                    test_flagB{2} = false &&
                     test_flagA{2} = false &&
                      Y'{2} = dummy_msg &&
                       B'{2} = dummy_part &&
                        x{1} = seed{1}[(X{1},A{1})] &&
                         (let l,l_0,l_1,l_2 = s{1} in
                          Y{1} = l_2 &&
                           X{1} = l_1 &&
                            B{1} = l_0 &&
                             A{1} = l &&
                              matchb{1} = false &&
                                ssskey{1} = dummy_session_key &&
                                 sstr{1} = dummy_string &&
                                  X'{1} = dummy_msg &&
                                   A'{1} = dummy_part &&
                                    eph_flagB{1} = false &&
                                     eph_flagA{1} = false &&
                                      Y'{1} = dummy_msg &&
                                       B'{1} = dummy_part &&
                                        ={s} && invariant1(LH{1},LH{2}) &&
                                                 invariant2(G{2},LH{1},
                                                            skey{2},seed{2}) &&
                                                  invariant3(G{2},LH{1},
                                                             LH{2},skey{2},
                                                             seed{2}) &&
                                                   ={b,bad,complete_sessions,incomplete_sessions,corrupt,pkey,skey,seed,LHT,tested_session}));[trivial|].*)
if.
  (* in_dom ((A,X),complete_sessions) *)
sp 5 6.
  if.
    (* B = B' && Y = Y' *)
    if.
      (* !in_dom ((B,Y),complete_sessions) *)
      ifneg 1 {2};if.
        inline{1} iH; expand invariant1,invariant2,invariant3;trivial.
     trivial.
     sp 5 7.

      ifneg 1 {2}.
    if.
    sp 2 1.
      ifneg 1 {2}.  
      if;[inline iH;trivial | trivial].
    ifneg 1 {2}.
    if.         
     inline iH;expand invariant1,invariant2,invariant3;trivial.   
    trivial.
  trivial.
 trivial.
save.

equiv Main_12 : AKE.Main ~ AKE1.Main : true ==> ={ res }
by auto
(invariant1(LH{1}, LH{2}) &&
 invariant2(G{2}, LH{1}, skey{2}, seed{2}) &&
 invariant3(G{2}, LH{1}, LH{2}, skey{2}, seed{2}) &&
( ={ b, bad, complete_sessions, incomplete_sessions, corrupt, pkey, skey, seed,
 LHT, tested_session })).

claim Pr12 : AKE.Main[res] = AKE1.Main[res] using Main_12.
