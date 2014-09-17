(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2014 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
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
open EcMaps
open EcUtils
open Big_int

(* -------------------------------------------------------------------- *)
type pexpr = 
  | PEc of big_int 
  | PEX of int
  | PEadd of pexpr * pexpr 
  | PEsub of pexpr * pexpr
  | PEmul of pexpr * pexpr
  | PEopp of pexpr 
  | PEpow of pexpr * int

let rec pp_pe fmt = function
  | PEc c -> Format.fprintf fmt "%s" (string_of_big_int c)
  | PEX i -> Format.fprintf fmt "x_%i" i
  | PEadd(p1,p2) -> Format.fprintf fmt "%a + %a" pp_pe p1 pp_pe p2
  | PEsub(p1,p2) -> Format.fprintf fmt "%a - %a" pp_pe p1 pp_pe p2
  | PEmul(p1,p2) -> Format.fprintf fmt "%a * %a" pp_pe p1 pp_pe p2
  | PEopp p -> Format.fprintf fmt "-%a" pp_pe p
  | PEpow(p,i) -> Format.fprintf fmt "%a^%i" pp_pe p i

let rec pexpr_eq (e1 : pexpr) (e2 : pexpr) : bool =
  match (e1,e2) with
  | (PEc c, PEc c') -> eq_big_int c c'
  | (PEX p1, PEX p2) -> p1 = p2
  | (PEadd (e3,e5), PEadd (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6
  | (PEsub (e3,e5), PEsub (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6 
  | (PEmul (e3,e5), PEmul (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6 
  | (PEopp e3, PEopp e4) -> pexpr_eq e3 e4
  | (PEpow (e3,n3), PEpow (e4,n4)) -> n3 = n4 && pexpr_eq e3 e4 
  | (_,_) -> false

let fv_pe = 
  let rec aux fv = function
    | PEc _        -> fv
    | PEX i        -> Sint.add i fv
    | PEadd(e1,e2) -> aux (aux fv e1) e2
    | PEsub(e1,e2) -> aux (aux fv e1) e2
    | PEmul(e1,e2) -> aux (aux fv e1) e2
    | PEopp e1     -> aux fv e1
    | PEpow(e1,_)  -> aux fv e1 in
  aux Sint.empty 

(* -------------------------------------------------------------------- *)
type 'a cmp_sub = [`Eq | `Lt | `Gt of 'a]
 
(* -------------------------------------------------------------------- *)
module type Coef = sig
  (* ------------------------------------------------------------------ *)
  type c 

  val cofint : big_int -> c
  val ctoint : c -> big_int

  val c0   : c
  val c1   : c
  val cadd : c -> c -> c
  val csub : c -> c -> c
  val cmul : c -> c -> c
  val copp : c -> c 
  val ceq  : c -> c -> bool
  val cdiv : c -> c -> c * c

  (* ------------------------------------------------------------------ *)
  type p 

  val pofint : int -> p
  val ptoint : p -> int 

  val padd : p -> p -> p
  val peq  : p -> p -> bool
  val pcmp : p -> p -> int 
  val pcmp_sub : p -> p -> p cmp_sub
end

(* -------------------------------------------------------------------- *) 
module Cint : Coef = struct
  type c = big_int

  let cofint c = c
  let ctoint c = c

  let c0 = zero_big_int
  let c1 = unit_big_int

  let cadd a b = add_big_int a b
  let csub a b = sub_big_int a b
  let cmul a b = mult_big_int a b
  let copp a   = minus_big_int a
  let ceq  a b = eq_big_int a b
  let cdiv a b = quomod_big_int a b
    
  type p = int

  let pofint p = p
  let ptoint p = p

  let padd (p1 : p) (p2 : p) = p1 + p2

  let peq (p1 : p) (p2 : p) = (p1 = p2)

  let pcmp (p1 : p) (p2 : p) : int = p1 - p2

  let pcmp_sub (p1 : p) (p2 : p) : p cmp_sub = 
    match pcmp p1 p2 with
    | c when c < 0 -> `Lt
    | 0            -> `Eq
    | _            -> `Gt (p1 - p2)

end

(* -------------------------------------------------------------------- *) 
module Cbool : Coef = struct
  type c = int

  let cofint c = 
    int_of_big_int (and_big_int unit_big_int (abs_big_int c))
  let ctoint c = big_int_of_int c
    
  let c0 = 0
  let c1 = 1

  let cadd x y = x lxor y
  let csub x y = x lxor y
  let cmul x y = x land y
  let copp x = x
  let ceq (x:c) y = x = y
  let cdiv x y = 
    assert (y <> 0);
    (x, 0)

  type p = unit

  let pofint p = 
    assert (1 <= p);
    ()

  let ptoint _p = 1

  let padd _p1 _p2 = ()

  let peq _p1 _p2 = true
  let pcmp _p1 _p2 = 0

  let pcmp_sub _p1 _p2 = `Eq

end

(* -------------------------------------------------------------------- *)
module type ModVal = sig
  val c : int option
  val p : int option
end

(* -------------------------------------------------------------------- *)
module Cmod (M : ModVal) : Coef = struct
  type c = big_int

  let correct_c =
    match M.c with
    | None    -> fun c -> c
    | Some cn -> 
        let cn = big_int_of_int cn in
          fun c -> mod_big_int c cn

  let cofint c = correct_c c
  let ctoint c = c

  let c0 = correct_c zero_big_int
  let c1 = correct_c unit_big_int

  let cadd a b = correct_c (add_big_int    a b)
  let csub a b = correct_c (sub_big_int    a b)
  let cmul a b = correct_c (mult_big_int   a b)
  let copp a   = correct_c (minus_big_int  a)

  let cdiv a b =
    let (q, r) = quomod_big_int a b in
    (correct_c q, correct_c r)

  let ceq a b  = eq_big_int a b
    
  type p = int

  let correct_p =
    match M.p with
    | None    -> fun p -> p
    | Some pn ->
        let rec doit p =
          if p < pn then p else doit (p / pn + p mod pn)
        in doit

  let pofint p = correct_p p
  let ptoint p = p

  let padd p1 p2 = correct_p (p1 + p2)

  let peq (p1 : p) (p2 : p) =
    p1 = p2

  let pcmp (p1 : p) (p2 : p) = p1 - p2

  let pcmp_sub = 
    match M.p with
    | None -> 
      fun (p1 : p) (p2 : p) ->
        begin match pcmp p1 p2 with
        | c when c < 0 -> `Lt
        | 0            -> `Eq
        | _            -> `Gt (p1 - p2)
        end
    | Some pn ->
      fun (p1 : p) (p2 : p) ->
        begin match pcmp p1 p2 with
        | c when c < 0 -> `Gt (p1 + (pn - p2) - 1)
        | 0 -> `Eq
        | _ -> `Gt (p1 - p2)
        end
end

(* -------------------------------------------------------------------- *)
module type Rnorm = sig
  module C : Coef 
    
  val norm_pe: pexpr -> (pexpr * pexpr) list -> pexpr
end

(* -------------------------------------------------------------------- *)
module Make (C : Coef) : Rnorm = struct
  open C

  module C = C

  module Var = struct
    type t = int
    let compare x y = x - y
    let eq x y = x == y
  end

  module Mon = struct
    type t = (Var.t * p) list

    let rec eq m1 m2 = 
      match m1, m2 with
      | [], [] -> true
      | (x1,p1)::m1, (x2,p2)::m2 ->
        Var.eq x1 x2 && peq p1 p2 && eq m1 m2
      | _, _ -> false
      
    let rec compare m1 m2 = 
      match m1, m2 with
      | [], [] ->  0
      | [], _  -> -1
      | _, []  ->  1
      | (x1,p1)::m1, (x2,p2)::m2 ->
        let cmp = Var.compare x1 x2 in
        if cmp = 0 then
          let cmp = pcmp p1 p2 in
          if cmp = 0 then compare m1 m2
          else cmp
        else cmp

    let p1 = pofint 1

    let one = []

    let cons x p m = (x,p) :: m

    let rec mul m1 m2 = 
      match m1, m2 with
      | [], _ -> m2
      | _, [] -> m1
      | (x1,p1 as xp1) :: m1', (x2,p2 as xp2) :: m2' ->
        match Var.compare x1 x2 with
        | c when c < 0 -> xp1 :: mul m1' m2
        | 0            -> cons x1 (padd p1 p2) (mul m1' m2')
        | _            -> xp2 :: mul m1 m2'

    (* factor m1 m2 = Some m  => m1 = m*m2 *)
    let rec factor m m1 m2 =
      match m1, m2 with
      | _, [] -> Some (List.rev_append m m1)
      | [], _ -> None
      | (x1,p1 as xp1) :: m1', (x2,p2) :: m2' ->
        match Var.compare x1 x2 with
        | c when c < 0 -> factor (xp1::m) m1' m2
        | 0            -> 
          begin match pcmp_sub p1 p2 with
          | `Lt -> None
          | `Eq -> factor m m1' m2'
          | `Gt p -> factor ((x1,p)::m) m1' m2'
          end
        | _            -> None 

    let factor m1 m2 = factor one m1 m2

    let degree m = 
      List.fold_left (fun i (_,p) -> i + ptoint p) 0 m

  end
        
  module Pol = struct
    type t = (c * Mon.t) list

    let rec eq p1 p2 = 
      match p1, p2 with
      | [], [] -> true
      | (c1,m1)::p1, (c2,m2)::p2 ->
        ceq c1 c2 && Mon.eq m1 m2 && eq p1 p2
      | _, _ -> false

    let rec opp p = 
      match p with
      | [] -> []
      | (c,m) :: p -> (copp c, m) :: opp p

    let cons c m p = 
      if ceq c c0 then p else (c,m)::p

    let rec add p1 p2 = 
      match p1, p2 with
      | [], _ -> p2
      | _, [] -> p1
      | (c1,m1 as cm1) :: p1', (c2,m2 as cm2) :: p2' ->
        match Mon.compare m1 m2 with
        | c when c < 0 -> cm1 :: add p1' p2
        | 0            -> cons (cadd c1 c2) m1 (add p1' p2')
        | _            -> cm2 :: add p1 p2'

    let rec sub p1 p2 = 
      match p1, p2 with
      | [], _ -> opp p2
      | _, [] -> p1
      | (c1,m1 as cm1) :: p1', (c2,m2) :: p2' ->
        match Mon.compare m1 m2 with
        | c when c < 0 -> cm1 :: sub p1' p2
        | 0            -> cons (csub c1 c2) m1 (sub p1' p2')
        | _            -> (copp c2, m2) :: sub p1 p2'
      
  
    let rec mul_mon ((c1,m1) as cm1) p = 
      match p with
      | [] -> []
      | (c2,m2) :: p -> add [cmul c1 c2, Mon.mul m1 m2] (mul_mon cm1 p)

     (* TODO: use (m1 + p1) * (m2 + p2) = m1m2 + (m1p2 + m2p1 + p1p2) ? *)
    let rec mul p1 p2 =
      match p1 with
      | [] -> []
      | cm1::p1 -> add (mul_mon cm1 p2) (mul p1 p2)

    let rec pow_int p n = 
      if n = 1 then p
      else 
        let r = pow_int p (n/2) in
        if n mod 2 = 0 then mul r r
        else mul p (mul r r)

    let pow p e = 
      let n = ptoint e in
      if n <= 0 then [c1, Mon.one] else pow_int p n 

    (* pexpr -> pol *)
    let zero = [] 
    let one = [c1,Mon.one]

    let cmon c m = 
      if ceq c c0 then zero else [c,m]

    let rec ofpexpr = function
      | PEc i -> cmon (cofint i) []
      | PEX x -> [ c1, [x, Mon.p1] ]
      | PEadd(p1,p2) -> add (ofpexpr p1) (ofpexpr p2)
      | PEsub(p1,p2) -> sub (ofpexpr p1) (ofpexpr p2)
      | PEmul(p1,p2) -> mul (ofpexpr p1) (ofpexpr p2)
      | PEopp p      -> opp (ofpexpr p)
      | PEpow(p,i)   -> pow (ofpexpr p) (pofint i)

    (* factorization by a monomial *)
        
    let cmfactor (c1,m1 as cm1) (c2,m2) =
      match Mon.factor m1 m2 with
      | None -> zero, [cm1]
      | Some m ->
        let q,r = cdiv c1 c2 in
        cmon q m, cmon r m1

    let rec factor p cm =
      match p with
      | [] -> zero, zero
      | cm'::p ->
        let cq,cr = cmfactor cm' cm in
        let pq,pr = factor p cm in
        add cq pq, add cr pr

    let rec rewrite1 p (cm,p' as rw) =
      let q,r = factor p cm in
      if eq q zero then r
      else 
        let p = add (mul q p') r in
        rewrite1 p rw

    let rec rewrites p rws =
      let p' = List.fold_left rewrite1 p rws in
      if eq p p' then p else rewrites p' rws
 
  end

  (* pol -> pexpr *)
  let xptopexpr (x,p) = 
    let x = PEX x in
    if peq p Mon.p1 then x else PEpow(x, ptoint p)

  let rec mtopexpr pe m = 
    match m with
    | [] -> pe
    | xp::m -> mtopexpr (PEmul(pe, xptopexpr xp)) m

  let cm1 = copp c1 

  let mtopexpr (c,m) =
    let i = ctoint c in
    let i' = abs_big_int i in
    let set_sign pe = if sign_big_int i < 0 then PEopp pe else pe in
    if eq_big_int i' unit_big_int then 
      begin match m with
      | [] -> set_sign (PEc i')
      | xp::m -> mtopexpr (set_sign (xptopexpr xp)) m
      end
    else mtopexpr (set_sign (PEc i')) m
      
  let rec topexpr pe p = 
    match p with
    | [] -> pe
    | cm :: p -> topexpr (PEadd(pe, mtopexpr cm)) p
      
  let topexpr p = 
    match p with
    | [] -> PEc(ctoint c0)
    | cm :: p -> topexpr (mtopexpr cm) p

  let rec get_mon p =
    match p with
    | [] -> c0, Mon.one, 0, Pol.zero
    | (c,m as cm)::p ->
      let (c',m',d',p') = get_mon p in
      let d = Mon.degree m in
      if d' < d then (c,m,d,p)
      else (c',m',d',cm::p')

  let mk_rw (pe1,pe2) = 
    let p1 = Pol.ofpexpr pe1 in
    let p2 = Pol.ofpexpr pe2 in
    let (c,m,_,p1') = get_mon p1 in
    if ceq c c0 || Mon.eq m Mon.one then 
      let (c,m,_,p2') = get_mon p2 in
      if ceq c c0 || Mon.eq m Mon.one then None 
      else Some ((c,m), Pol.sub p1 p2')
    else Some ((c,m), Pol.sub p2 p1')
 
  let norm_pe pe lpe = 
    let rws = List.pmap mk_rw lpe in
    let p = Pol.ofpexpr pe in
    topexpr (Pol.rewrites p rws)

end

(* -------------------------------------------------------------------- *)
module Iring : Rnorm = Make(Cint)
module Bring : Rnorm = Make(Cbool)

(* -------------------------------------------------------------------- *)
type c = big_int

let c0 = zero_big_int
let c1 = unit_big_int

let cadd a b = add_big_int a  b
let csub a b = sub_big_int a  b
let cmul a b = mult_big_int a  b
let copp a   = minus_big_int a
let ceq  a b = eq_big_int a b
let cdiv a b = quomod_big_int a b
