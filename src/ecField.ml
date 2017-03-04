(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2017 - Inria
 *
 * Distributed under the terms of the CeCILL-C-V1 license
 * -------------------------------------------------------------------- *)

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
open EcRing
open EcBigInt.Notations

module BI = EcBigInt

(* -------------------------------------------------------------------- *)
type fexpr =
| FEc   of c
| FEX   of int
| FEadd of fexpr * fexpr
| FEsub of fexpr * fexpr
| FEmul of fexpr * fexpr
| FEopp of fexpr
| FEinv of fexpr
| FEdiv of fexpr * fexpr
| FEpow of fexpr * BI.zint

(* -------------------------------------------------------------------- *)
type rsplit = pexpr * pexpr * pexpr

let left   ((t,_,_) : rsplit) : pexpr = t
let right  ((_,_,t) : rsplit) : pexpr = t
let common ((_,t,_) : rsplit) : pexpr = t

(* -------------------------------------------------------------------- *)
let npepow x n =
  if BI.equal n BI.zero then PEc c1 else
  if BI.equal n BI.one  then x else
    match x with
    | PEc c -> begin
             if ceq c c1 then PEc c1
        else if ceq c c0 then PEc c0
        else try  PEc (BI.pow c (BI.to_int n))
             with BI.Overflow -> PEpow (x, n)
    end
    | _ -> PEpow (x, n)

(* -------------------------------------------------------------------- *)
let rec npemul (x : pexpr) (y : pexpr) : pexpr =
  match x,y with
  | PEc c, PEc c' -> PEc (cmul c c')
  | PEc c, _ ->
         if ceq c c1 then y
    else if ceq c c0 then PEc c0
    else PEmul (x,y)
  | _, PEc c ->
         if ceq c c1 then x
    else if ceq c c0 then PEc c0
    else PEmul (x,y)
  | PEpow (e1,n1), PEpow (e2,n2) ->
      if   BI.equal n1 n2
      then npepow (npemul e1 e2) n1
      else PEmul (x,y)
  | _,_ -> PEmul (x,y)

(* -------------------------------------------------------------------- *)
let rec isin (e1 : pexpr) (p1 : BI.zint) (e2 : pexpr) (p2 : BI.zint) =
  match e2 with
  | PEmul (e3, e4) -> begin
    match isin e1 p1 e3 p2 with
    | Some (p, e5) when BI.sign p = 0 ->
        Some (p, npemul e5 (npepow e4 p2))
    | Some (p, e5) -> begin
        match isin e1 p e4 p2 with
        | Some (n, e6) -> Some (n, npemul e5 e6)
        | None -> Some (p, npemul e5 (npepow e4 p2))
    end
    | None ->
      match isin e1 p1 e4 p2 with
      | Some (n,e5) -> Some (n,npemul (npepow e3 p2) e5)
      | None -> None
  end

  | PEpow (e3, p3) ->
      if   BI.sign p3 = 0
      then None
      else isin e1 p1 e3 (p3 *^ p2)

  | _ ->
    if pexpr_eq e1 e2 then
      match BI.compare p1 p2 with
      | c when c > 0 -> Some (p1-^p2, PEc c1)
      | c when c < 0 -> Some (BI.zero, npepow e2 (p2-^p1))
      | _ -> Some (BI.zero, PEc c1)
    else None

(* -------------------------------------------------------------------- *)
let rec split_aux (e1 : pexpr) (p : BI.zint) (e2 : pexpr) : rsplit =
  match e1 with
  | PEmul (e3, e4) ->
      let r1 = split_aux e3 p e2 in
      let r2 = split_aux e4 p (right r1) in
      (npemul (left   r1) (left   r2),
       npemul (common r1) (common r2),
       right r2)

  | PEpow (e3, p3) ->
      if   BI.sign p3 = 0
      then (PEc c1, PEc c1, e2)
      else split_aux e3 (p3 *^ p) e2

  | _ ->
    match isin e1 p e2 BI.one with
    | Some (q, e3) ->
        if   BI.sign q = 0
        then (PEc c1, npepow e1 p, e3)
        else (npepow e1 q, npepow e1 (p -^ q), e3)
    | None -> (npepow e1 p, PEc c1, e2)

let split e1 e2 = split_aux e1 BI.one e2

(* -------------------------------------------------------------------- *)
type linear = (pexpr * pexpr * (pexpr list))

let num       (t,_,_) = t
let denum     (_,t,_) = t
let condition (_,_,t) = t

(* -------------------------------------------------------------------- *)
let npeadd (e1 : pexpr) (e2 : pexpr) =
  match (e1, e2) with
  | (PEc c, PEc c') -> PEc (cadd c c')
  | (PEc c, _) -> if (ceq c c0) then e2 else PEadd (e1, e2)
  | (_, PEc c) -> if (ceq c c0) then e1 else PEadd (e1, e2)
  | _ -> PEadd (e1, e2)

(* -------------------------------------------------------------------- *)
let npesub e1 e2 =
  match (e1,e2) with
  | (PEc c, PEc c') -> PEc (csub c c')
  | (PEc c, _ ) -> if (ceq c c0) then PEopp e2 else PEsub (e1, e2)
  | ( _, PEc c) -> if (ceq c c0) then e1 else PEsub (e1, e2)
  | _ -> PEsub (e1, e2)

(* -------------------------------------------------------------------- *)
let npeopp e1 =
  match e1 with PEc c -> PEc (copp c) | _ -> PEopp e1

(* -------------------------------------------------------------------- *)
let rec fnorm (e : fexpr) : linear =
  match e with
  | FEc c -> (PEc c, PEc c1, [])
  | FEX x -> (PEX x, PEc c1, [])

  | FEadd (e1, e2) ->
    let x = fnorm e1 in
    let y = fnorm e2 in
    let s = split (denum x) (denum y) in
    (npeadd (npemul (num x) (right s)) (npemul (num y) (left s)),
     npemul (left s) (npemul (right s) (common s)),
     condition x @ condition y)

  | FEsub (e1,e2) ->
    let x = fnorm e1 in
    let y = fnorm e2 in
    let s = split (denum x) (denum y) in
    (npesub (npemul (num x) (right s)) (npemul (num y) (left s)),
     npemul (left s) (npemul (right s) (common s)),
     condition x @ condition y)

  | FEmul (e1,e2) ->
    let x = fnorm e1 in
    let y = fnorm e2 in
    let s1 = split (num x) (denum y) in
    let s2 = split (num y) (denum x) in
    (npemul (left s1) (left s2),
     npemul (right s2) (right s1),
     condition x @ condition y)

  | FEopp e1 ->
    let x = fnorm e1 in
    (npeopp (num x), denum x, condition x)

  | FEinv e ->
    let x = fnorm e in
    (denum x, num x, (num x) :: (condition x))

  | FEdiv (e1,e2) ->
    let x = fnorm e1 in
    let y = fnorm e2 in
    let s1 = split (num x) (num y) in
    let s2 = split (denum x) (denum y) in
    (npemul (left s1) (right s2),
     npemul (left s2) (right s1),
     (num y) :: ((condition x) @ (condition y)))

  | FEpow (e1,n) ->
    let x = fnorm e1 in
    (npepow (num x) n, npepow (denum x) n, condition x)
