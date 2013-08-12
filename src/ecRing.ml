(* Copyright The Coq Development Team, 1999-2010
 * Copyright INRIA - CNRS - LIX - LRI - PPS, 1999-2010
 *
 * This file is distributed under the terms of the:
 *   GNU Lesser General Public License Version 2.1
 *
 * This file originates from the `Coq Proof Assistant'
 * It has been modified for the needs of EasyCrypt
 *)

(* -------------------------------------------------------------------- *)
open Big_int

type c = big_int

let c0 = zero_big_int
let c1 = unit_big_int

let cadd a b = add_big_int a  b
let csub a b = sub_big_int a  b
let cmul a b = mult_big_int a  b
let copp a =  minus_big_int a
let ceq a b = eq_big_int a b
let cdiv a b = quomod_big_int a b

type pexpr = PEc of c 
  | PEX of int
  | PEadd of pexpr * pexpr 
  | PEsub of pexpr * pexpr
  | PEmul of pexpr * pexpr
  | PEopp of pexpr 
  | PEpow of pexpr * int

type pol = Pc of c 
  | Pinj of int * pol
  | PX of pol * int * pol

type mon = Mon0 | Zmon of (int * mon) | Vmon of (int * mon)


let rec pexpr_eq (e1 : pexpr) (e2 : pexpr) : bool =
  match (e1,e2) with
    | (PEc c, PEc c') -> ceq c c'
    | (PEX p1, PEX p2) -> p1 = p2
    | (PEadd (e3,e5), PEadd (e4,e6)) -> 
      if (pexpr_eq e3 e4) then pexpr_eq e5 e6 else false
    | (PEsub (e3,e5), PEsub (e4,e6)) -> 
      if (pexpr_eq e3 e4) then pexpr_eq e5 e6 else false
    | (PEmul (e3,e5), PEmul (e4,e6)) -> 
      if (pexpr_eq e3 e4) then pexpr_eq e5 e6 else false
    | (PEopp e3, PEopp e4) -> pexpr_eq e3 e4
    | (PEpow (e3,n3), PEpow (e4,n4)) -> 
      if (n3 = n4) then pexpr_eq e3 e4 else false
    | (_,_) -> false

(**)

let p0 = Pc c0
let p1 = Pc c1

let mkXi i = PX (p1,i,p0) (* 1 * x_0 ^ i + 0  *)

let mkX = mkXi 1 (* ~= x ^ 1 *)

let mkPinj_pred j p = 
  if (j=1) then p else Pinj(j-1,p)

let mk_X j = mkPinj_pred j mkX

let rec peq (p : pol) (q:pol) : bool =
  match (p,q) with
    | (Pc c1, Pc c2) -> ceq c1 c2
    | (Pinj (j1,q1),Pinj (j2,q2)) -> if (j1 = j2) then peq q1 q2 else false
    | (PX (p1,i1,q1), PX (p2,i2,q2)) -> if (i1 = i2) then
                                            if (peq p1 p2) then
                                                    peq q1 q2
                                            else false
                                        else false
    | _ -> false

let mkPinj (j : int) (p : pol) : pol =
	match p with
		| Pc _ -> p
		| Pinj (j',q) -> Pinj ((j+j'),q)
		| _ -> Pinj (j,p)

let mkPX p i q =
	match p with
		| Pc c -> if (ceq c c0) then
						mkPinj 1 q 
					else PX (p,i,q)
		| Pinj _ -> PX (p,i,q)
		| PX (p',i',q') -> if (peq q' p0) then
							PX (p',(i+i'),q)
							else PX (p,i,q) 

(* Opposite  *)

let rec popp ( p : pol) : pol =
  match p with
    | Pc c -> Pc (copp c)
    | Pinj (j,q) -> Pinj (j, popp q)
    | PX (p,j,q) -> PX (popp p, j, popp q)

let (--~) p = popp p

(* Addition and Subs *)

let rec paddc (p : pol) (c : c) : pol =
  match p with
    | Pc c' -> Pc (cadd c' c)
    | Pinj (j,q) -> Pinj (j,paddc q c)
    | PX (p,j,q) -> PX (p,j, paddc q c)

let rec psubc (p : pol) (c : c) : pol =
  match p with
    | Pc c' -> Pc (csub c' c)
    | Pinj (j,q) -> Pinj (j,psubc q c)
    | PX (p,j,q) -> PX (p,j, psubc q c)

let rec padd (p : pol) (p' : pol) : pol =
  match p' with
    | Pc c -> paddc p c
    | Pinj (j',q') -> paddi q' j' p
    | PX (p',i',q') ->  match p with
                          | Pc c ->  PX (p',i',paddc q' c)
                          | Pinj (j,q) -> if (j = 1) then
                                            PX (p',i', padd q q') 
                                          else
                                            PX (p',i', padd (Pinj (j-1,q)) q')
                          | PX (p,i,q) -> if (i = i') then
                                            mkPX (padd p p') i (padd q q')
                                          else if (i > i') then
                                                mkPX (padd (PX (p,i-i',p0)) p') i' (padd q q')
                                               else
                                                mkPX (paddx p' (i'-i) p) i (padd q q')
and paddi (q : pol) (j : int)  (p : pol) : pol =
  match p with
    | Pc c -> mkPinj j (paddc q c)
    | Pinj (j',q') -> if (j' = j) then
                        mkPinj j (padd q' q)
                      else if (j' > j) then
                            mkPinj j (padd (Pinj (j'-j,q')) q)
                           else
                            mkPinj j' (paddi q (j-j') q')
    | PX (p,i,q') -> if (j = 1) then
                        PX (p,i,padd q' q)
                     else PX (p,i,paddi q (j-1) q')
and paddx (p' : pol) (i' : int) (p : pol) : pol =
  match p with
    | Pc _ ->  PX (p',i',p)
    | Pinj (j,q') -> if (j=1) then
                      PX (p',i',q')
                     else PX (p',i', Pinj (j-1,q'))
    | PX (p,i,q') -> if (i=i') then
                      mkPX (padd p p') i q'
                     else if (i > i') then
                            mkPX (padd (PX (p,(i-i'),p0)) p') i' q'
                          else
                            mkPX (paddx p' (i'-i) p) i q'

let rec psub (p : pol) (p' : pol) : pol =
  match p' with
    | Pc c -> psubc p c
    | Pinj (j',q') -> psubi q' j' p
    | PX (p',i',q') -> match p with
                        | Pc c -> PX (popp p' , i', paddc (popp q') c)
                        | Pinj (j,q) -> if (j=1) then
                                          PX (popp p',i',psub q q') 
                                        else PX (popp p',i', psub (Pinj (j-1,q)) q')
                        | PX (p,i,q) -> if (i = i') then
                                          mkPX  (psub p p') i (psub q q')
                                        else if (i > i') then
                                              mkPX (psub (PX (p,i-i',p0)) p') i' (psub q q')
                                             else
                                              mkPX (psubx p' (i'-i) p) i (psub q q')
and psubi (q : pol) (j : int) ( p : pol) : pol =
  match p with
    | Pc c -> mkPinj j (paddc (popp q) c)
    | Pinj (j',q') -> if ( j' = j ) then mkPinj j (psub q' q)
                      else if (j' > j) then
                              mkPinj j (psub (Pinj (j' - j,q')) q)   
                           else
                              mkPinj j' (psubi q (j-j') q')
    | PX (p,i,q') -> if (j = 1) then
                      PX (p,i,psub q' q) 
                     else PX (p,i, psubi q (j-1) q')
and psubx (p' : pol) (i' : int) (p : pol) : pol =
  match p with
    | Pc _ -> PX (popp p,i',p)
    | Pinj (j,q') -> if (j = 1) then
                       PX (popp p',i',q') 
                     else PX (popp p',i', Pinj (j-1,q'))
    | PX (p,i,q') -> if (i = i') then 
                        mkPX (psub p p') i q'
                     else if (i > i') then
                             mkPX (psub (PX (p,i-i',p0)) p') i' q'
                          else
                             mkPX (psubx p' (i' -i)  p) i q'

let rec pmulc_aux (p : pol) (c : c) :pol =
  match p with
    | Pc c' -> Pc (cmul c' c)
    | Pinj (j,q) -> mkPinj j (pmulc_aux q c)
    | PX (p,i,q) -> mkPX (pmulc_aux p c) i (pmulc_aux q c)

let pmulc (p : pol) (c :c ) : pol =
  if (ceq c c0) then p0 else if (ceq c c1) then p else pmulc_aux p c

let rec pmul (p : pol) (p'' : pol) : pol =
  match p'' with
    | Pc c -> pmulc p c
    | Pinj (j',q') -> pmuli q' j' p
    | PX (p',i',q') -> match p with
                        | Pc c -> pmulc p'' c
                        | Pinj (j,q) -> let qq' = if (j = 1) then pmul q q' else pmul (Pinj (j-1,q)) q' in
                          mkPX (pmul p p') i' qq'
                        | PX (p,i,q) -> let qq' = pmul q q' in
                                        let pq' = pmuli q' 1 p in
                                        let qp' = pmul (mkPinj 1 q) p' in
                                        let pp' = pmul p p' in
                                        padd (mkPX (padd (mkPX pp' i p0) qp') i' p0) (mkPX pq' i qq')
and pmuli (q : pol) (j : int) (p:pol) : pol =
  match p with
    | Pc c -> mkPinj j (pmulc q c)
    | Pinj (j',q') -> if (j' = j) then mkPinj j (pmul q' q) else
                      if (j' > j) then mkPinj j (pmul (Pinj (j'-j,q')) q) else
                                       mkPinj j' (pmuli q (j-j') q')
    | PX (p',i',q') -> if (j = 1) then mkPX (pmuli q 1 p') i' (pmul q' q) else
                       mkPX (pmuli q j p') i' (pmuli q (j-1) q')

let rec ppow_pos (res : pol) (p : pol) (t : int) : pol =
  if (t = 1) then pmul res p else
          ppow_pos (pmul res p) p (t-1)
let rec ppow_n (p : pol) (n : int) : pol =
  if (n = 0) then p1 else ppow_pos p1 p n

(* Monomial *)

let mkZmon j m =
  match m with
    | Mon0 -> Mon0
    | _ -> Zmon (j,m)

let zmon_pred j m =
  if (j = 1) then m else mkZmon (j-1) m
 
let mkVmon i m =
  match m with
    | Mon0 -> Vmon (i,Mon0)
    | Zmon (j,m) -> Vmon (i,(zmon_pred j m))
    | Vmon (i',m) -> Vmon ((i+i'),m)

let rec cfactor (p : pol) ( c : c) : (pol * pol) =
  match p with
    | Pc c' ->
      let (q,r) = cdiv c' c in
        (Pc r, Pc q) 
    | Pinj (j1,p1) ->
      let (r,s) = cfactor p1 c in
        (mkPinj j1 r, mkPinj j1 s)
    | PX (p1,i,q1) ->
      let (r1,s1) = cfactor p1 c in
      let (r2,s2) = cfactor q1 c in
        (mkPX r1 i r2, mkPX s1 i s2)

let rec mfactor (p : pol) (c : c) (m : mon) : pol * pol =
  match (p,m) with
    | (_, Mon0) ->
      if (ceq c c1) then (Pc c0, p) else cfactor p c
    | (Pc _, _) -> (p, Pc c0)
    | (Pinj (j1,p1), Zmon (j2,m1)) ->
      if (j1 = j2) then
        let (r,s) = mfactor p1 c m1 in
          (mkPinj j1 r, mkPinj j1 s)
      else if (j1 < j2) then
            let (r,s) = mfactor p1 c (Zmon ((j2-j1),m1)) in
              (mkPinj j1 r, mkPinj j1 s)
           else (p, Pc c0)
    | (Pinj _ , Vmon _) -> (p, Pc c0)
    | (PX (p1,i,q1), Zmon (j,m1)) ->
      let m2 = zmon_pred j m1 in
      let (r1,s1) = mfactor p1 c m in
      let (r2,s2) = mfactor q1 c m2 in
        (mkPX r1 i r2, mkPX s1 i s2)
    | (PX (p1,i,q1), Vmon (j,m1)) ->
      if (i = j) then
        let (r1,s1) = mfactor p1 c (mkZmon 1 m1) in
          (mkPX r1 i q1, s1)
      else if ( j > i) then
            let (r1,s1) = mfactor p1 c (Vmon (j-i,m1)) in
              (mkPX r1 i q1, s1)
           else
            let (r1,s1) = mfactor p1 c (mkZmon 1 m1) in
              (mkPX r1 i q1, mkPX s1 (i-j) (Pc c0))

let ponesubst (p1 : pol) ((c,m1) : c * mon) (p2 : pol) : pol option =
  let (q1,r1) = mfactor p1 c m1 in
  match r1 with
    | Pc c -> if (ceq c c0) then None
                else Some (padd q1 (pmul p2 r1))
    | _ -> Some (padd q1 (pmul p2 r1))

let rec pnsubstl (p1 : pol) (cm1 : c * mon) (p2 : pol) (n : int) : pol =
  match (ponesubst p1 cm1 p2) with
    | Some p3 -> if (n = 0) then p3 else
                  pnsubstl p3 cm1 p2 (n-1)
    | _ -> p1
 
let pnsubst (p1 : pol) (cm1 : c * mon) (p2 :pol) (n : int) : pol option =
  match (ponesubst p1 cm1 p2) with
    | Some p3 -> if (n = 0) then None
                  else Some (pnsubstl p3 cm1 p2 (n-1))
    | _ -> None

let rec psubstl1 (p1 : pol) (lm1 : ((c * mon) * pol) list ) (n : int) : pol =
  match lm1 with
    | [] -> p1
    | (m1,p2) :: lm2 -> psubstl1 (pnsubstl p1 m1 p2 n) lm2 n

let rec psubstl (p1 : pol) (lm1 : ((c * mon) * pol) list) (n : int) : pol option =
  match lm1 with
    | [] -> None
    | (m1,p2) :: lm2 -> 
      match pnsubst p1 m1 p2 n with
        | Some p3 -> Some (psubstl1 p3 lm2 n)
        | None -> psubstl p1 lm2 n

let rec pnsubstl (p1 : pol) (lm1 : ((c * mon) * pol) list) (m : int) (n : int) : pol =
  match psubstl p1 lm1 n with
    | Some p3 -> if (m = 0) then p3 else pnsubstl p3 lm1 (m-1) n
    | _ -> p1
 
let rec norm_aux (e : pexpr) : pol =
  match e with
    | PEc c -> Pc c
    | PEX i -> mk_X i
    | PEadd (PEopp e1, e2) -> psub (norm_aux e2) (norm_aux e1) 
    | PEadd (e1, PEopp e2) -> psub (norm_aux e1) (norm_aux e2)
    | PEadd (e1,e2) -> padd (norm_aux e1) (norm_aux e2)
    | PEmul (e1,e2) -> pmul (norm_aux e1) (norm_aux e2)
    | PEsub (e1,e2) -> psub (norm_aux e1) (norm_aux e2)
    | PEopp e1 -> popp (norm_aux e1)
    | PEpow (e1,p) -> ppow_n (norm_aux e1) p 

let norm_subst (n : int) (lmp : ((c * mon) * pol) list) (p : pexpr) : pol  =  pnsubstl (norm_aux p) lmp n n

let rec mon_of_pol (p : pol) : (c * mon) option =
  match p with
    | Pc c -> if (ceq c c0) then None else Some (c, Mon0)
    | Pinj (j,p) ->
      (match mon_of_pol p with
        | None -> None
        | Some (c,m) -> Some (c, mkZmon j m))
    | PX (p,i,q) ->
      if (peq q p0) then
         match mon_of_pol p with
          | None -> None
          | Some (c,m) -> Some (c, mkVmon i m)
      else None

let rec mk_monpol_list (lpe : (pexpr * pexpr) list) : ((c * mon) * pol) list =
  match lpe with
    | [] -> []
    | (me,pe) :: lpe ->
      match mon_of_pol (norm_subst 0 [] me) with
        | None -> mk_monpol_list lpe
        | Some m -> (m,norm_subst 0 [] pe) :: mk_monpol_list lpe

let norm p lp = norm_subst (List.length lp) (mk_monpol_list lp) p
