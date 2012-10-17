include "ake_proof_reduction55'.ec".
timeout 3.
pred indexes(cantKG,cant_KG_C,indexA_C,indexB_C : int) = 
(0 <= cant_KG_C && cant_KG_C <= indexA_C => cantKG = 0) &&
(indexA_C < cant_KG_C && cant_KG_C <= indexB_C => cantKG = 1) &&
(indexB_C < cant_KG_C  => cantKG = 2).

print out_noclash.

axiom out_no_dummy : forall (a : eph_key, sk : secret_key), out_noclash(sk,a) <> dummy_message.
axiom inp_no_dummy : forall (a : eph_key, sk : secret_key), inp(sk,a) <> dummy_message.

axiom gpk_iny : forall (x1,x2 : secret_key),
                gen_public_key(x1) = gen_public_key(x2) => x1 = x2.

(* invariant is split into 3 situations: *)
(* - before we reach indexA *)
(* - after we reach indexA, but before we reach indexB *)
(* - after we reach indexB *)

pred stateInvs
(complete_sessions    : complete_session_with_status,
 incomplete_sessions  : incomplete_session_with_status,
 corrupt               : (part, bool) map,
 pkey                  : (part, public_key) map,
 skey                  : (part, secret_key) map,
 seed                  : (message * part, eph_key) map) =
(forall (A : part, X : message), in_dom((A,X),complete_sessions) => in_dom(A,skey)) &&
(forall (A : part, X : message), in_dom((A,X),incomplete_sessions) => in_dom(A,skey)) &&
(forall (A : part, X : message), in_dom((A,X),complete_sessions) => in_dom((X,A),seed)) &&
(forall (A : part, X : message), in_dom((A,X),incomplete_sessions) => in_dom((X,A),seed)) &&
(forall (A : part, X : message), in_dom((X,A),seed) => in_dom(A,skey)).

pred inv1 
(complete_sessions1    : complete_session_with_status,
 incomplete_sessions1  : incomplete_session_with_status,
 corrupt               : (part, bool) map,
 pkey                  : (part, public_key) map,
 skey                  : (part, secret_key) map,
 seed1                 : (message * part, eph_key) map,
 complete_sessions_C   : complete_session_with_status,
 incomplete_sessions_C : incomplete_session_with_status,
 corrupt_C             : (part, bool) map,
 pkey_C                : (part, public_key) map,
 skey_C                : (part, secret_key) map,
 seed_C                : (message * part, eph_key) map,
 complete_sessions2    : complete_session_with_status,
 incomplete_sessions2  : incomplete_session_with_status,
 seed2                 : (message * part, eph_key) map,
 cantKG,cant_KG_C,indexA_C,indexB_C : int,
 pkA, pkB, fstpart_C, sndpart_C : part,
 skA, skB              : secret_key,
 corruptA, corruptB     : bool) =
 cant_KG_C <= indexA_C => 
     cantKG = 0 && 
     complete_sessions1 = complete_sessions_C &&
     incomplete_sessions1 = incomplete_sessions_C &&
     skey = skey_C &&
     corrupt = corrupt_C &&
     seed1 = seed_C  &&
     complete_sessions2 = empty_map &&
     incomplete_sessions2 = empty_map &&
     seed2 = empty_map.


pred inv2 
(complete_sessions1     : complete_session_with_status,
 incomplete_sessions1   : incomplete_session_with_status,
 corrupt                : (part, bool) map,
 pkey                   : (part, public_key) map,
 skey                   : (part, secret_key) map,
 seed1                  : (message * part, eph_key) map,
 complete_sessions_C    : complete_session_with_status,
 incomplete_sessions_C  : incomplete_session_with_status,
 corrupt_C              : (part, bool) map,
 pkey_C                 : (part, public_key) map,
 skey_C                 : (part, secret_key) map,
 seed_C                 : (message * part, eph_key) map,
 complete_sessions2     : complete_session_with_status,
 incomplete_sessions2   : incomplete_session_with_status,
 seed2                  : (message * part, eph_key) map,
 cantKG,cant_KG_C,indexA_C,indexB_C : int,
 pkA, pkB, fstpart_C, sndpart_C : part,
 skA, skB               : secret_key,
 corruptA, corruptB     : bool) =
 indexA_C <  cant_KG_C  && cant_KG_C <= indexB_C =>     
      (  cantKG = 1  && (skey = skey_C[pkA <- skA] && !in_dom(pkA,skey_C)) 
      && (pkA = fstpart_C && pkA = gen_public_key(skA))
      (* && (forall (A : part,X:message), in_dom((A,X),complete_sessions1) => *)
      (*  ((A = fstpart_C) && in_dom((A,X),complete_sessions2)) || *)
      (*  (A <> fstpart_C && in_dom((A,X),complete_sessions_C) && *)
      (*   complete_sessions1[(A,X)] = complete_sessions_C[(A,X)])) *)
      && complete_sessions1 = complete_sessions_C       
      && (forall (X:message), in_dom((fstpart_C,X),complete_sessions2) =>  
                              (in_dom((fstpart_C,X),complete_sessions_C) &&
                              session_eph_flag(complete_sessions2[(fstpart_C,X)])=
                              session_eph_flag(complete_sessions_C[(fstpart_C,X)])))
      && (forall (X:message), in_dom((fstpart_C,X),complete_sessions_C) =>  
                              in_dom((fstpart_C,X),complete_sessions2))
      (* && (forall (A : part,X:message), in_dom((A,X),incomplete_sessions1) => *)
      (*  (A = fstpart_C) && in_dom((A,X),incomplete_sessions2)  || *)
      (*  (A <> fstpart_C && in_dom((A,X),incomplete_sessions_C) && *)
      (*   incomplete_sessions1[(A,X)] = incomplete_sessions_C[(A,X)])) *)
      && incomplete_sessions1 = incomplete_sessions_C 
      && (forall (X:message), in_dom((fstpart_C,X),incomplete_sessions2) =>  
                              (in_dom((fstpart_C,X),incomplete_sessions_C)&& 
                              snd(incomplete_sessions2[(fstpart_C,X)])=
                              snd(incomplete_sessions_C[(fstpart_C,X)])))
      && (forall (X:message), in_dom((fstpart_C,X),incomplete_sessions_C) =>  
                              in_dom((fstpart_C,X),incomplete_sessions2))
      && (forall (A : part,X:message), in_dom((X,A),seed1) =>
         ((A = fstpart_C) => (in_dom((X,A),seed2) && 
           seed1[(X,A)] = seed2[(X,A)])) &&
         (A <> fstpart_C => (in_dom((X,A),seed_C) &&
          seed1[(X,A)] = seed_C[(X,A)])))
      && (forall (A : part,X:message), in_dom((X,A),seed_C) =>
         in_dom((X,A),seed1))
      && (forall (A : part,X:message), in_dom((X,A),seed2) =>
         (in_dom((X,A),seed1) && seed1[(X,A)] = seed2[(X,A)]))
      && (forall (X:message), !in_dom ((X,fstpart_C),seed_C))
      && (forall (A : part,X:message), in_dom((X,A),seed_C) => (in_dom((X,A),seed1)))
      && corrupt = corrupt_C 
      && corrupt_C[fstpart_C] = corruptA).


pred inv3
(complete_sessions1    : complete_session_with_status,
 incomplete_sessions1  : incomplete_session_with_status,
 corrupt               : (part, bool) map,
 pkey                  : (part, public_key) map,
 skey                  : (part, secret_key) map,
 seed1                 : (message * part, eph_key) map,
 complete_sessions_C   : complete_session_with_status,
 incomplete_sessions_C : incomplete_session_with_status,
 corrupt_C             : (part, bool) map,
 pkey_C                : (part, public_key) map,
 skey_C                : (part, secret_key) map,
 seed_C                : (message * part, eph_key) map,
 complete_sessions2    : complete_session_with_status,
 incomplete_sessions2  : incomplete_session_with_status,
 seed2                 : (message * part, eph_key) map,
 cantKG,cant_KG_C,indexA_C,indexB_C : int,
 pkA, pkB, fstpart_C, sndpart_C : part,
 skA, skB              : secret_key,
 corruptA, corruptB     : bool) =
 indexB_C <  cant_KG_C  => 
     (  cantKG = 2 && sndpart_C <> fstpart_C
      && (skey = skey_C[pkA <- skA][pkB <- skB]&& !in_dom(pkA,skey_C)
          && !in_dom(pkB,skey_C) && pkA <> pkB)  
      && (pkA = fstpart_C && pkA = gen_public_key(skA))
      && (pkB = sndpart_C && pkB = gen_public_key(skB)) 
       (*&&  (forall (A : part,X:message), in_dom((A,X),complete_sessions1) => *)
       (* ((A = fstpart_C || A = sndpart_C) && in_dom((A,X),complete_sessions2)) || *)
       (* (A <> fstpart_C && A <> sndpart_C && in_dom((A,X),complete_sessions_C) && *)
       (*  complete_sessions1[(A,X)] = complete_sessions_C[(A,X)])) *)
      && complete_sessions1 = complete_sessions_C
      && (forall (X:message), in_dom((fstpart_C,X),complete_sessions2) =>  
                              (in_dom((fstpart_C,X),complete_sessions_C) &&
                              session_eph_flag(complete_sessions2[(fstpart_C,X)])=
                              session_eph_flag(complete_sessions_C[(fstpart_C,X)])))
      && (forall (X:message), in_dom((sndpart_C,X),complete_sessions2) =>  
                              (in_dom((sndpart_C,X),complete_sessions_C) && 
                              session_eph_flag(complete_sessions2[(sndpart_C,X)])=
                              session_eph_flag(complete_sessions_C[(sndpart_C,X)])))
      && (forall (X:message), in_dom((fstpart_C,X),complete_sessions_C) =>  
                              in_dom((fstpart_C,X),complete_sessions2))
      && (forall (X:message), in_dom((sndpart_C,X),complete_sessions_C) =>  
                              in_dom((sndpart_C,X),complete_sessions2))
      (* && (forall (A : part,X:message), in_dom((A,X),incomplete_sessions1) => *)
      (*  (A = fstpart_C || A = sndpart_C) && in_dom((A,X),incomplete_sessions2)  || *)
      (*  (A <> fstpart_C && A <> sndpart_C && in_dom((A,X),incomplete_sessions_C) && *)
      (*   incomplete_sessions1[(A,X)] = incomplete_sessions_C[(A,X)])) *)
      && incomplete_sessions1 = incomplete_sessions_C
      && (forall (X:message), in_dom((fstpart_C,X),incomplete_sessions2) =>  
                              (in_dom((fstpart_C,X),incomplete_sessions_C) && 
                              snd(incomplete_sessions2[(fstpart_C,X)])=
                              snd(incomplete_sessions_C[(fstpart_C,X)])))
      && (forall (X:message), in_dom((sndpart_C,X),incomplete_sessions2) =>  
                              (in_dom((sndpart_C,X),incomplete_sessions_C)&& 
                              snd(incomplete_sessions2[(sndpart_C,X)])=
                              snd(incomplete_sessions_C[(sndpart_C,X)])))
      && (forall (X:message), in_dom((fstpart_C,X),incomplete_sessions_C) =>  
                              in_dom((fstpart_C,X),incomplete_sessions2))
      && (forall (X:message), in_dom((sndpart_C,X),incomplete_sessions_C) =>  
                              in_dom((sndpart_C,X),incomplete_sessions2))
      && (forall (A : part,X:message), in_dom((X,A),seed1) =>
         ((A = fstpart_C || A = sndpart_C) => (in_dom((X,A),seed2) && 
           seed1[(X,A)] = seed2[(X,A)])) &&
         (A <> fstpart_C && A <> sndpart_C=> (in_dom((X,A),seed_C) &&
          seed1[(X,A)] = seed_C[(X,A)])))      
      && (forall (A : part,X:message), in_dom((X,A),seed_C) =>
         in_dom((X,A),seed1))
      && (forall (A : part,X:message), in_dom((X,A),seed2) =>
         (in_dom((X,A),seed1) && seed1[(X,A)] = seed2[(X,A)]))
      && (forall (X:message), !in_dom ((X,fstpart_C),seed_C))
      && (forall (X:message), !in_dom ((X,sndpart_C),seed_C))) 
      && (forall (A : part,X:message), in_dom((X,A),seed_C) => (in_dom((X,A),seed1))) 
      && corrupt = corrupt_C      
      && corrupt_C[fstpart_C] = corruptA
      && corrupt_C[sndpart_C] = corruptB.

pred stateinvr 
(complete_sessions2          : complete_session_with_status,
 incomplete_sessions2        : incomplete_session_with_status,
 indexA_C,indexB_C,cant_KG_C : int,
 seed2                       : (message * part, eph_key) map,
 fstpart_C,sndpart_C         : part ) =
(forall (A : part,X:message), in_dom((A,X),incomplete_sessions2) 
                              => ((A = fstpart_C && cant_KG_C > indexA_C) 
                                 ||(A = sndpart_C && cant_KG_C > indexB_C))) && 
(forall (A : part,X:message), in_dom((A,X),complete_sessions2) 
                              => ((A = fstpart_C && cant_KG_C > indexA_C) 
                                 ||(A = sndpart_C && cant_KG_C > indexB_C)))&&
(forall (A : part,X:message),(in_dom((A,X),complete_sessions2) ||
                              in_dom((A,X),incomplete_sessions2)) =>
                              in_dom((X,A),seed2)). 

       
axiom map_extensional_equality : 
 forall(m1, m2 : ('a , 'b) map), (m1 = m2 <=> 
 (forall (x : 'a), (in_dom(x,m1) <=> in_dom(x,m2)) &&
                   (in_dom(x,m1) => (m1[x] = m2[x])))).

pred inv (complete_sessions1    : complete_session_with_status,
 incomplete_sessions1  : incomplete_session_with_status,
 corrupt               : (part, bool) map,
 pkey                  : (part, public_key) map,
 skey                  : (part, secret_key) map,
 seed1                 : (message * part, eph_key) map,
 complete_sessions_C   : complete_session_with_status,
 incomplete_sessions_C : incomplete_session_with_status,
 corrupt_C             : (part, bool) map,
 pkey_C                : (part, public_key) map,
 skey_C                : (part, secret_key) map,
 seed_C                : (message * part, eph_key) map,
 complete_sessions2    : complete_session_with_status,
 incomplete_sessions2  : incomplete_session_with_status,
 seed2                 : (message * part, eph_key) map,
 cantKG,cant_KG_C,indexA_C,indexB_C : int,
 pkA, pkB, fstpart_C, sndpart_C : part,
 skA, skB              : secret_key,
 corruptA, corruptB     : bool) = 
(0 <= cant_KG_C && indexA_C < indexB_C &&
stateInvs(complete_sessions1, incomplete_sessions1,  corrupt,pkey,skey,
     seed1) && 
stateinvr(complete_sessions2,incomplete_sessions2,indexA_C,indexB_C,
          cant_KG_C,seed2,fstpart_C,sndpart_C) &&
inv1(complete_sessions1, incomplete_sessions1,  corrupt,pkey,skey,
     seed1,complete_sessions_C, incomplete_sessions_C,  corrupt_C,
     pkey_C,skey_C,seed_C,complete_sessions2, incomplete_sessions2,
     seed2,cantKG,cant_KG_C,indexA_C,indexB_C,pkA,pkB,fstpart_C,
     sndpart_C,skA,skB,corruptA,corruptB)  && 
inv2(complete_sessions1, incomplete_sessions1,  corrupt,pkey,skey,
     seed1,complete_sessions_C, incomplete_sessions_C,  corrupt_C,
     pkey_C,skey_C,seed_C,complete_sessions2, incomplete_sessions2,
     seed2,cantKG,cant_KG_C,indexA_C,indexB_C,pkA,pkB,fstpart_C,
     sndpart_C,skA,skB,corruptA,corruptB)  && 
inv3(complete_sessions1, incomplete_sessions1,  corrupt,pkey,skey,
     seed1,complete_sessions_C, incomplete_sessions_C,  corrupt_C,
     pkey_C,skey_C,seed_C,complete_sessions2, incomplete_sessions2,
     seed2,cantKG,cant_KG_C,indexA_C,indexB_C,pkA,pkB,fstpart_C,
     sndpart_C,skA,skB,corruptA,corruptB)).

equiv KG :
AKE5.KG ~ AKE5'_red.KG_C :
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && 
(bad_C{1} =  bad_C{2}) && !bad_C{1} ==>
(bad_C{1} = bad_C{2})&& (!bad_C{1} => 
 inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={res}).
expand inv.
inline.
if{2}.
  if{2}.
   trivial.
   if{2}.
    trivial.    
    trivial.   
  if{2}.
    if{2}.
     trivial.    
     if{2}.
      expand inv3;trivial.
      trivial. 
    expand inv2,inv3;trivial.
save.

equiv INIT : AKE5.Init ~ AKE5'_red.Init_C :
 inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && ={A,B} &&
(bad_C{1} = bad_C{2}) && !bad_C{1} ==>
(bad_C{1} = bad_C{2}) && (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})) && ={res}.
expand inv.
case{2}: (cant_KG_C <= indexA_C).
app 3 2 bad_C{1} = bad_C{2} && (bad_C{1} <> true =>
        0 <= cant_KG_C{2} &&
         indexA_C{2} < indexB_C{2} &&
          stateInvs(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                    pkey{1},skey{1},seed{1}) &&
                 stateinvr(complete_sessions{2},incomplete_sessions{2},indexA_C{2},
                     indexB_C{2},cant_KG_C{2},seed{2},fstpart_C{2},sndpart_C{2}) &&
           ={X} && inv1(complete_sessions{1},incomplete_sessions{1},
                        corrupt{1},pkey{1},skey{1},seed{1},
                        complete_sessions_C{2},incomplete_sessions_C{2},
                        corrupt_C{2},pkey_C{2},skey_C{2},seed_C{2},
                        complete_sessions{2},incomplete_sessions{2},seed{2},
                        cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                        pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) &&
                        cant_KG_C{2} <= indexA_C{2}) && !bad_C{1};
          [| condf{2};condf{2};trivial].
sp 1 2;condt{2};trivial.
sp 1 2;condf{2}.
case{2}:cant_KG_C <= indexB_C.
 
app 3 1 bad_C{1} = bad_C{2} && (bad_C{1} <> true =>
        0 <= cant_KG_C{2} &&
         indexA_C{2} < indexB_C{2} &&
          stateInvs(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                    pkey{1},skey{1},seed{1}) &&
           stateinvr(complete_sessions{2},incomplete_sessions{2},indexA_C{2},
                     indexB_C{2},cant_KG_C{2},seed{2},fstpart_C{2},sndpart_C{2}) &&
           ={X} && inv2(complete_sessions{1},incomplete_sessions{1},
                         corrupt{1},pkey{1},skey{1},seed{1},
                         complete_sessions_C{2},incomplete_sessions_C{2},
                         corrupt_C{2},pkey_C{2},skey_C{2},seed_C{2},
                         complete_sessions{2},incomplete_sessions{2},seed{2},
                         cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                         pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},
                         skB{2},corruptA{2},corruptB{2}) && cant_KG_C{2} > indexA_C{2} &&  
                         cant_KG_C{2} <= indexB_C{2}) && !bad_C{1};[|condf{2};trivial].
condt{2}.
if{2};[|condt{2}]. 
inline;derandomize;rnd >>;trivial.
expand inv2;trivial.
trivial.
expand inv2;trivial.
condf{2}.
condt{2}.
if{2}.
inline{2} at 0.
sp 1 2;rnd>>.
sp 1 2.
condt{2}.
condt{1}.
sp 3 2.
if.
sp 3 4.
condt{2}.
expand inv3;trivial.
trivial.
if{2}.
inline{2} at 0.
sp 1 2;rnd>>.
sp 1 2.
condf{2}.
condt{1}.
sp 3 2.
if.
sp 3 4.
condt{2}.
trivial.
expand inv3;trivial.
trivial.
rnd>>.
if.
sp 3 3.
if.
trivial.
expand inv3;trivial.
trivial.
trivial.
save.

equiv RESP : AKE5.Respond ~ AKE5'_red.Respond_C :
 inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={A,B,X}
     && (bad_C{1} = bad_C{2}) && !bad_C{1} ==>
(bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={res}).
expand inv.
sp 2 1.
case{2}: (cant_KG_C <= indexA_C).
app 3 1 bad_C{1} = bad_C{2} && (bad_C{1} <> true =>
        0 <= cant_KG_C{2} &&
         indexA_C{2} < indexB_C{2} &&
          stateInvs(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                    pkey{1},skey{1},seed{1}) &&
stateinvr(complete_sessions{2},incomplete_sessions{2},indexA_C{2},indexB_C{2},
 cant_KG_C{2},seed{2},fstpart_C{2},sndpart_C{2}) &&
           ={X, Y} && inv1(complete_sessions{1},incomplete_sessions{1},
                        corrupt{1},pkey{1},skey{1},seed{1},
                        complete_sessions_C{2},incomplete_sessions_C{2},
                        corrupt_C{2},pkey_C{2},skey_C{2},seed_C{2},
                        complete_sessions{2},incomplete_sessions{2},seed{2},
                        cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                        pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) &&
                        cant_KG_C{2} <= indexA_C{2}) && !bad_C{1};
          [| condf{2};condf{2};trivial].
condt{2}.
if;[|trivial].
rnd>>;sp 2 2.
if;trivial.

condf{2}.
case{2}:cant_KG_C <= indexB_C.
 
app 3 1 bad_C{1} = bad_C{2} && (bad_C{1} <> true =>
        0 <= cant_KG_C{2} &&
         indexA_C{2} < indexB_C{2} &&
          stateInvs(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                    pkey{1},skey{1},seed{1}) &&
stateinvr(complete_sessions{2},incomplete_sessions{2},indexA_C{2},indexB_C{2},
          cant_KG_C{2},seed{2},fstpart_C{2},sndpart_C{2}) &&
           ={X, Y} && inv2(complete_sessions{1},incomplete_sessions{1},
                         corrupt{1},pkey{1},skey{1},seed{1},
                         complete_sessions_C{2},incomplete_sessions_C{2},
                         corrupt_C{2},pkey_C{2},skey_C{2},seed_C{2},
                         complete_sessions{2},incomplete_sessions{2},seed{2},
                         cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                         pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},
                         skB{2},corruptA{2},corruptB{2}) && cant_KG_C{2} > indexA_C{2} &&  
                         cant_KG_C{2} <= indexB_C{2}) && !bad_C{1};[|condf{2};trivial].
condt{2}.
if{2}.
if.
inline{2} at 0.
sp.
rnd >>.
sp 2 2.
condt{2}.
sp 1 2.
if.
sp 3 4.
condt{2};sp 1 2;condf{2}.
trivial.
expand inv2;trivial.
sp 2 3.
!2 condf{2}.
trivial.
sp.
condf{2};trivial.
if{2}.
if.
rnd>>.
sp 2 2.
if;[|trivial].
trivial.
expand inv2.
trivial.
trivial.
condf{1};trivial.

condf{2}.
condt{2}.
if{2}.
inline.
condt{1}.
sp 1 3.
rnd >>.
sp 1 2.
condt{2}.
sp 2 2.
if.
sp 3 4.
condt{2}.
trivial.
expand inv3;trivial.
trivial.
trivial.
if{2}.
condt{1}.
inline.
sp.
rnd>>.
sp 2 2.
condf{2}.
sp 1 2.
if.
sp 3 4.
condt{2}.
trivial.
expand inv3;trivial.
trivial.

if.
rnd>>.
sp 2 2.
if.
trivial;expand inv3;trivial.
trivial.
trivial.
save.

equiv COMP :
AKE5.Complete ~ AKE5'_red.Complete_C :
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && (bad_C{1} = bad_C{2}) 
     && !bad_C{1} && ={A,B,X,Y} ==>
(bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
 inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})).
expand inv.
if;[|trivial].
sp 3 3;if;[|trivial].
sp 1 2;if{2};[|trivial].
if{2}.
inline.
sp 1 4.
condt{2}.
condt{2}.
sp 1 2.
condt{2}.
trivial.
expand inv2;trivial.
expand inv3;trivial.

inline.
sp 1 4.
condf{2}.
condt{2}.
sp 1 2.
condt{2}.
trivial.
expand inv3;trivial.
expand inv2;trivial.
expand inv3;trivial.
save.

equiv Corrupt :
AKE5.Corrupt ~ AKE5'_red.Corrupt_C : 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && (bad_C{1} = bad_C{2}) 
     && !bad_C{1} && ={A} ==>
(bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={res}).
expand inv.
sp 2 2.
if{2}.
condt{1};inline;trivial.
if{2}.
condt{1};inline;trivial.
if;trivial.
save.

equiv EPHKEYREVEAL :
AKE5.EphKeyReveal ~ AKE5'_red.EphKeyReveal_C : 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && (bad_C{1} = bad_C{2}) 
     && !bad_C{1} && ={A,X} ==>
(bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={res}).
expand inv.
sp 5 6.
if{2}.
if.
if.
trivial.
expand inv2;trivial.
expand inv3;trivial.
if.
trivial.
expand inv2;trivial.
expand inv3;trivial.
trivial.
trivial.

inline.
if.
if{2}.
sp 1 7.
condt{2}.
sp 1 2.
condt{2}.
if.
sp 1 8.
condt{2}.
expand inv2;trivial.
expand inv3;trivial.
if.
sp 1 5.
condf{2}.
condt{2}.
trivial.
expand inv3;trivial.
expand inv2;trivial.
trivial.
sp 1 7.
condf{2}.
sp 1 2.
condt{2}.
if.
sp 1 8.
condt{2}.
expand inv3;trivial.
if.
sp 1 5.
condf{2}.
condt{2}.
trivial.
expand inv3;trivial.
sp 1 2.
!2 condf{2}.
trivial.
trivial.
save.

equiv Adv : AKE5.B ~ AKE5'_red.B :
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && (bad_C{1} = bad_C{2}) 
 && !bad_C{1} ==>
(bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={res})
by auto upto (bad_C) with
((bad_C{1} = bad_C{2} )&& (!bad_C{1} =>
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}))).

print wingame5'.


pred wingame5_pred
(sid : session_id,
 str : session_string,
 corrupt : (part, bool) map,
 complete_session : complete_session_with_status,
 incomplete_session : incomplete_session_with_status) =
eqS_oracle(str,sid) && 
(fresh_sid1(sid,corrupt,complete_session,incomplete_session) ||
 fresh_sid11(sid,corrupt,complete_session,incomplete_session) ||
 fresh_sid2(sid,corrupt) ||
 fresh_sid3(sid,corrupt,complete_session,incomplete_session)
).


equiv Main :
AKE5.Main ~ AKE5'_red.Main : true ==> ={bad_C} && (!bad_C{1} => 
((wingame5_pred(fst(res){1}, snd(res){1},corrupt{1},complete_sessions{1},incomplete_sessions{1}))
&& fstpart(fst(res)){1} = pkA{2} && cant_KG_C{2} > indexB_C{2}
&& sndpart(fst(res)){1} = pkB{2}
 =>
(wingame5'(fst(res{2}), snd(res{2}),corruptA{2},corruptB{2},complete_sessions{2},incomplete_sessions{2},pkA{2},pkB{2})))).
inline.
sp.
!2 rnd>>{2}.
case{2}: indexB_C = indexA_C.
admit.
app 0 2 inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},pkA{2},pkB{2},fstpart_C{2},
     sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2})  && (bad_C{1} = bad_C{2}) 
 && !bad_C{1}.
trivial.
app 1 2 (bad_C{1} = bad_C{2} )&& (!bad_C{1} => 
inv(complete_sessions{1}, incomplete_sessions{1},  corrupt{1},pkey{1},skey{1},
     seed{1},complete_sessions_C{2}, incomplete_sessions_C{2},  corrupt_C{2},
     pkey_C{2},skey_C{2},seed_C{2},complete_sessions{2}, incomplete_sessions{2},
     seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
     pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},corruptA{2},corruptB{2}) && ={sidss}).
wp.
call using Adv.
trivial.
trivial.
expand inv,wingame5',wingame5_pred.
trivial.
app 0 0 
={bad_C} && (bad_C{1} <> true =>
       (0 <= cant_KG_C{2} &&
         indexA_C{2} < indexB_C{2} &&
          stateInvs(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                    pkey{1},skey{1},seed{1}) &&
           stateinvr(complete_sessions{2},incomplete_sessions{2},indexA_C{2},
                     indexB_C{2},cant_KG_C{2},seed{2},fstpart_C{2},
                     sndpart_C{2}) &&
            inv1(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                 pkey{1},skey{1},seed{1},complete_sessions_C{2},
                 incomplete_sessions_C{2},corrupt_C{2},pkey_C{2},skey_C{2},
                 seed_C{2},complete_sessions{2},incomplete_sessions{2},
                 seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                 pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},
                 corruptA{2},corruptB{2}) &&
             inv2(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                  pkey{1},skey{1},seed{1},complete_sessions_C{2},
                  incomplete_sessions_C{2},corrupt_C{2},pkey_C{2},skey_C{2},
                  seed_C{2},complete_sessions{2},incomplete_sessions{2},
                  seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                  pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},
                  corruptA{2},corruptB{2}) &&
              inv3(complete_sessions{1},incomplete_sessions{1},corrupt{1},
                   pkey{1},skey{1},seed{1},complete_sessions_C{2},
                   incomplete_sessions_C{2},corrupt_C{2},pkey_C{2},skey_C{2},
                   seed_C{2},complete_sessions{2},incomplete_sessions{2},
                   seed{2},cantKG{2},cant_KG_C{2},indexA_C{2},indexB_C{2},
                   pkA{2},pkB{2},fstpart_C{2},sndpart_C{2},skA{2},skB{2},
                   corruptA{2},corruptB{2})) &&
        ={sidss}) &&
(bad_C{1} <> true => eqS_oracle (snd (sidss{1}),fst (sidss{1})) =>
        fresh_sid1(fst (sidss{1}),corrupt{1},complete_sessions{1},
                   incomplete_sessions{1}) => cant_KG_C{2} > indexB_C{2} =>
        fstpart (fst (sidss{1})) = pkA{2} =>
        sndpart (fst (sidss{1})) = pkB{2} =>
        fresh_sid1g5'(fst (sidss{2}),corruptA{2},corruptB{2},
                      complete_sessions{2},incomplete_sessions{2})) &&
(bad_C{1} <> true => eqS_oracle (snd (sidss{1}),fst (sidss{1})) =>
        fresh_sid11(fst (sidss{1}),corrupt{1},complete_sessions{1},
                   incomplete_sessions{1}) => cant_KG_C{2} > indexB_C{2} =>
        fstpart (fst (sidss{1})) = pkA{2} =>
        sndpart (fst (sidss{1})) = pkB{2} =>
        fresh_sid11g5'(fst (sidss{2}),corruptA{2},corruptB{2},
                      complete_sessions{2},incomplete_sessions{2}))&&
(bad_C{1} <> true => eqS_oracle (snd (sidss{1}),fst (sidss{1})) =>
        fresh_sid2(fst (sidss{1}),corrupt{1}) => cant_KG_C{2} > indexB_C{2} =>
        fstpart (fst (sidss{1})) = pkA{2} =>
        sndpart (fst (sidss{1})) = pkB{2} =>
        fresh_sid2g5'(fst (sidss{2}),corruptA{2},corruptB{2})) &&
(bad_C{1} <> true => eqS_oracle (snd (sidss{1}),fst (sidss{1})) =>
        fresh_sid3(fst (sidss{1}),corrupt{1},complete_sessions{1},
                   incomplete_sessions{1}) => (cant_KG_C > indexB_C){2} =>
        fstpart (fst (sidss{1})) = pkA{2} =>
        sndpart (fst (sidss{1})) = pkB{2} =>
        fresh_sid3g5'(fst (sidss{2}),corruptA{2},corruptB{2},
                      complete_sessions{2},incomplete_sessions{2})).
trivial.
trivial.
save.

