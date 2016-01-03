(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2016 - Inria
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
open EcMaps
open EcUtils

module BI = EcBigInt

open EcBigInt.Notations

(* -------------------------------------------------------------------- *)
type pexpr = 
  | PEc   of BI.zint
  | PEX   of int
  | PEadd of pexpr * pexpr 
  | PEsub of pexpr * pexpr
  | PEmul of pexpr * pexpr
  | PEopp of pexpr 
  | PEpow of pexpr * BI.zint

let rec pp_pe fmt = function
  | PEc c        -> Format.fprintf fmt "%a" BI.pp_print c
  | PEX i        -> Format.fprintf fmt "x_%i" i
  | PEadd(p1,p2) -> Format.fprintf fmt "%a + %a" pp_pe p1 pp_pe p2
  | PEsub(p1,p2) -> Format.fprintf fmt "%a - %a" pp_pe p1 pp_pe p2
  | PEmul(p1,p2) -> Format.fprintf fmt "%a * %a" pp_pe p1 pp_pe p2
  | PEopp p      -> Format.fprintf fmt "-%a" pp_pe p
  | PEpow(p,i)   -> Format.fprintf fmt "%a^%a" pp_pe p BI.pp_print i

let rec pexpr_eq (e1 : pexpr) (e2 : pexpr) : bool =
  match (e1,e2) with
  | (PEc c, PEc c') -> BI.equal c c'
  | (PEX p1, PEX p2) -> p1 = p2
  | (PEadd (e3,e5), PEadd (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6
  | (PEsub (e3,e5), PEsub (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6 
  | (PEmul (e3,e5), PEmul (e4,e6)) -> pexpr_eq e3 e4 && pexpr_eq e5 e6 
  | (PEopp e3, PEopp e4) -> pexpr_eq e3 e4
  | (PEpow (e3,n3), PEpow (e4,n4)) -> BI.equal n3 n4 && pexpr_eq e3 e4 
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
exception Overflow

(* -------------------------------------------------------------------- *)
module type Coef = sig
  (* ------------------------------------------------------------------ *)
  type c 

  val cofint : BI.zint -> c
  val ctoint : c -> BI.zint

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

  val pofint  : BI.zint -> p
  val ptoint  : p -> BI.zint

  val padd : p -> p -> p
  val peq  : p -> p -> bool
  val pcmp : p -> p -> int 
  val pcmp_sub : p -> p -> p cmp_sub
end

(* -------------------------------------------------------------------- *) 
module Cint : Coef = struct
  type c = BI.zint

  let cofint = (identity : BI.zint -> c)
  let ctoint = (identity : c -> BI.zint)

  let c0 : c = BI.zero
  let c1 : c = BI.one

  let cadd = (BI.add   : c -> c -> c)
  let csub = (BI.sub   : c -> c -> c)
  let cmul = (BI.mul   : c -> c -> c)
  let copp = (BI.neg   : c -> c)
  let cdiv = (BI.ediv  : c -> c -> c * c)
  let ceq  = (BI.equal : c -> c -> bool)

  type p = BI.zint

  let pofint = (identity : BI.zint -> p)
  let ptoint = (identity : p -> BI.zint)

  let padd = (BI.add     : c -> c -> c)
  let peq  = (BI.equal   : c -> c -> bool)
  let pcmp = (BI.compare : c -> c -> int)

  let pcmp_sub (p1 : p) (p2 : p) : p cmp_sub = 
    match BI.compare p1 p2 with
    | c when c < 0 -> `Lt
    | 0 -> `Eq
    | _ -> `Gt (p1 -^ p2)
end

(* -------------------------------------------------------------------- *) 
module Cbool : Coef = struct
  type c = int

  let cofint (c : BI.zint) =
    if BI.sign c = 0 then 0 else 1

  let ctoint (c : int) =
    if c == 0 then BI.zero else BI.one
    
  let c0 : c = 0
  let c1 : c = 1

  let cadd = ((lxor)   : c -> c -> c)
  let csub = ((lxor)   : c -> c -> c)
  let cmul = ((land)   : c -> c -> c)
  let copp = (identity : c -> c)
  let ceq  = ((=)      : c -> c -> bool)

  let cdiv (x : c) (y : c) : c * c = 
    if y == 0 then raise Division_by_zero; (x, 0)

  type p = unit

  let pofint  (_p : BI.zint) = assert (BI.one <=^ _p); ()
  let ptoint  (_p : p) = BI.one

  let padd = (fun (_ : p) (_ : p) -> ())
  let peq  = (fun (_ : p) (_ : p) -> true)
  let pcmp = (fun (_ : p) (_ : p) -> 0)

  let pcmp_sub _p1 _p2 = `Eq

end

(* -------------------------------------------------------------------- *)
module type ModVal = sig
  val c : BI.zint option
  val p : BI.zint option
end

(* -------------------------------------------------------------------- *)
module Cmod (M : ModVal) : Coef = struct
  type c = BI.zint

  let correct_c : c -> c =
    match M.c with
    | None   -> fun x -> x
    | Some c -> fun x -> BI.erem x c

  let cofint c = correct_c c
  let ctoint c = c

  let c0 = correct_c BI.zero
  let c1 = correct_c BI.one

  let cadd a b = correct_c (a +^ b)
  let csub a b = correct_c (a -^ b)
  let cmul a b = correct_c (a *^ b)
  let copp a   = correct_c (~^ a)

  let cdiv a b =
    let (q, r) = BI.ediv a b in
    (correct_c q, correct_c r)

  let ceq = (BI.equal : c -> c -> bool)
    
  type p = BI.zint

  let correct_p : p -> p =
    match M.p with
    | None    -> fun p -> p
    | Some pn ->
        let rec doit p =
          if p <^ pn then p else
            let (q, r) = BI.ediv p pn in doit (q +^ r)
        in doit

  let pofint  (p : BI.zint) = correct_p p
  let ptoint  (p : p) = p

  let padd p1 p2 = correct_p (p1 +^ p2)

  let peq  = (BI.equal   : p -> p -> bool)
  let pcmp = (BI.compare : p -> p -> int)

  let pcmp_sub : p -> p -> p cmp_sub =
    match M.p with
    | None -> 
      fun (p1 : p) (p2 : p) -> begin
        match BI.compare p1 p2 with
        | c when c < 0 -> `Lt
        | 0 -> `Eq
        | _ -> `Gt (p1 -^ p2)
      end

    | Some pn ->
      fun (p1 : p) (p2 : p) -> begin
        match BI.compare p1 p2 with
        | c when c < 0 -> `Gt (BI.pred (p1 +^ (pn -^ p2)))
        | 0 -> `Eq
        | _ -> `Gt (p1 -^ p2)
      end
end

(* -------------------------------------------------------------------- *)
module type Rnorm = sig
  module C : Coef 
    
  val norm_pe: pexpr -> (pexpr * pexpr) list -> pexpr
end

(* -------------------------------------------------------------------- *)
module Make (C : Coef) : Rnorm = struct
  module C = C

  module Var = struct
    type t = int

    let compare = (compare : t -> t -> int)
    let eq = ((==) : t -> t -> bool)
  end

  module Mon = struct
    type t = (Var.t * C.p) list

    let rec eq (m1 : t) (m2 : t) =
      match m1, m2 with
      | (x1,p1)::m1, (x2,p2)::m2 ->
          Var.eq x1 x2 && C.peq p1 p2 && eq m1 m2

      | [], [] -> true
      | _ , _  -> false
      
    let rec compare (m1 : t) (m2 : t) =
      match m1, m2 with
      | [], [] ->  0
      | [], _  -> -1
      | _, []  ->  1
      | (x1,p1)::m1, (x2,p2)::m2 -> begin
          match Var.compare x1 x2 with
          | n when n <> 0 -> n
          | _ ->
            match C.pcmp p1 p2 with
            | n when n <> 0 -> n
            | _ -> compare m1 m2
      end

    let one : t =
      []

    let cons (x : Var.t) (p : C.p) (m : t) : t =
      (x, p) :: m

    let rec mul m1 m2 = 
      match m1, m2 with
      | [], _ -> m2 | _, [] -> m1

      | ((x1, p1) as xp1) :: m1', ((x2, p2) as xp2) :: m2' ->
          match Var.compare x1 x2 with
          | c when c < 0 -> xp1 :: mul m1' m2
          | c when c > 0 -> xp2 :: mul m1 m2'
          | _ -> cons x1 (C.padd p1 p2) (mul m1' m2')

    (* factor m1 m2 = Some m  => m1 = m*m2 *)
    let rec factor m m1 m2 =
      match m1, m2 with
      | _, [] -> Some (List.rev_append m m1)
      | [], _ -> None
      | (x1,p1 as xp1) :: m1', (x2,p2) :: m2' ->
        match Var.compare x1 x2 with
        | c when c < 0 -> factor (xp1::m) m1' m2
        | c when c > 0 -> None
        | _ -> begin
            match C.pcmp_sub p1 p2 with
            | `Lt -> None
            | `Eq -> factor m m1' m2'
            | `Gt p -> factor ((x1,p)::m) m1' m2'
        end

    let factor m1 m2 = factor [] m1 m2

    let degree m = 
      List.fold_left (fun i (_, p) -> i +^ C.ptoint p) BI.zero m
  end
        
  module Pol = struct
    type t = (C.c * Mon.t) list

    let rec eq (p1 : t) (p2 : t) = 
      match p1, p2 with
      | (c1,m1)::p1, (c2,m2)::p2 ->
          C.ceq c1 c2 && Mon.eq m1 m2 && eq p1 p2

      | [], [] -> true
      | _ , _  -> false

    let zero : t = [] 
    let one  : t = [C.c1, Mon.one]

    let cmon (c : C.c) (m : Mon.t) : t =
      if C.ceq c C.c0 then zero else [c, m]

    let cons (c : C.c) (m : Mon.t) (p : t) : t =
      if C.ceq c C.c0 then p else (c, m)::p

    let rec add (p1 : t) (p2 : t) : t = 
      match p1, p2 with
      | [], _  -> p2
      | _ , [] -> p1
      | ((c1, m1) as cm1) :: p1', ((c2, m2) as cm2) :: p2' ->
        match Mon.compare m1 m2 with
        | c when c < 0 -> cm1 :: add p1' p2
        | c when c > 0 -> cm2 :: add p1 p2'
        | _ -> cons (C.cadd c1 c2) m1 (add p1' p2')

    let rec opp (p : t) : t = 
      List.map (fst_map C.copp) p

    let rec sub (p1 : t) (p2 : t) : t =
      match p1, p2 with
      | [], _  -> opp p2
      | _ , [] -> p1
      | (c1,m1 as cm1) :: p1', (c2,m2) :: p2' ->
        match Mon.compare m1 m2 with
        | c when c < 0 -> cm1 :: sub p1' p2
        | c when c > 0 -> (C.copp c2, m2) :: sub p1 p2'
        | _ -> cons (C.csub c1 c2) m1 (sub p1' p2')

    let rec mul =
      let rec mul_mon ((c1, m1) as cm1) (p : t) : t=
        match p with
        | [] -> []
        | (c2, m2) :: p -> add [C.cmul c1 c2, Mon.mul m1 m2] (mul_mon cm1 p)
      in fun (p1 : t) (p2 : t) ->
           match p1 with
           | [] -> []
           | cm1::p1 -> add (mul_mon cm1 p2) (mul p1 p2)

    let rec pow_int p n = 
      if BI.equal n BI.one then p else
        let r = pow_int p (BI.rshift n 1) in
        match BI.parity n with
        | `Even -> mul r r
        | `Odd  -> mul p (mul r r)

    let pow p e = 
      let n = C.ptoint e in
      if BI.sign n <= 0 then [C.c1, Mon.one] else pow_int p n 

    (* pexpr -> pol *)
    let rec ofpexpr = function
      | PEc i        -> cmon (C.cofint i) []
      | PEX x        -> [C.c1, [x, C.pofint BI.one]]
      | PEadd(p1,p2) -> add (ofpexpr p1) (ofpexpr p2)
      | PEsub(p1,p2) -> sub (ofpexpr p1) (ofpexpr p2)
      | PEmul(p1,p2) -> mul (ofpexpr p1) (ofpexpr p2)
      | PEopp p      -> opp (ofpexpr p)
      | PEpow(p,i)   -> pow (ofpexpr p) (C.pofint i)

    (* factorization by a monomial *)
    let cmfactor (c1, m1 as cm1) (c2, m2) =
      match Mon.factor m1 m2 with
      | None   -> zero, [cm1]
      | Some m -> let (q, r) = C.cdiv c1 c2 in (cmon q m, cmon r m1)

    let rec factor (p : t) (cm : C.c * Mon.t) : t * t =
      match p with
      | [] ->
          (zero, zero)
      | cm'::p ->
          let (cq, cr) = cmfactor cm' cm in
          let (pq, pr) = factor p cm in
          (add cq pq, add cr pr)

    type rw = (C.c * Mon.t) * t

    let rec rewrite1 (p : t) (cm, p' as rw : rw) : t =
      let (q, r) = factor p cm in
      if   eq q zero
      then r
      else let p = add (mul q p') r in  rewrite1 p rw

    let rec rewrites (p : t) (rws : rw list) : t =
      let p' = List.fold_left rewrite1 p rws in
      if eq p p' then p else rewrites p' rws
  end

  (* pol -> pexpr *)
  let xptopexpr (x, p) = 
    if   C.peq p (C.pofint BI.one)
    then PEX x
    else PEpow (PEX x, C.ptoint p)

  let rec mtopexpr pe m = 
    match m with
    | []    -> pe
    | xp::m -> mtopexpr (PEmul (pe, xptopexpr xp)) m

  let mtopexpr (c, m) =
    let i  = C.ctoint c in
    let i' = BI.abs i in
    let set_sign pe = if BI.sign i < 0 then PEopp pe else pe in
    if BI.equal i' BI.one then  begin
      match m with
      | [] -> set_sign (PEc i')
      | xp::m -> mtopexpr (set_sign (xptopexpr xp)) m
    end else
      mtopexpr (set_sign (PEc i')) m
      
  let rec topexpr pe p = 
    match p with
    | [] -> pe
    | cm :: p -> topexpr (PEadd(pe, mtopexpr cm)) p
      
  let topexpr p = 
    match p with
    | [] -> PEc (C.ctoint C.c0)
    | cm :: p -> topexpr (mtopexpr cm) p

  let rec get_mon p =
    match p with
    | [] -> (C.c0, Mon.one, BI.zero, Pol.zero)
    | (c, m as cm) :: p ->
      let (c', m', d', p') = get_mon p in
      let d = Mon.degree m in
      if   d' <^ d
      then (c , m , d , p)
      else (c', m', d', cm::p')

  let mk_rw (pe1,pe2) = 
    let p1 = Pol.ofpexpr pe1 in
    let p2 = Pol.ofpexpr pe2 in
    let (c,m,_,p1') = get_mon p1 in
    if C.ceq c C.c0 || Mon.eq m Mon.one then begin
      let (c,m,_,p2') = get_mon p2 in
      if   C.ceq c C.c0 || Mon.eq m Mon.one
      then None 
      else Some ((c,m), Pol.sub p1 p2')
    end else
      Some ((c,m), Pol.sub p2 p1')
 
  let norm_pe pe lpe = 
    let rws = List.pmap mk_rw lpe in
    let p   = Pol.ofpexpr pe in
    topexpr (Pol.rewrites p rws)
end

(* -------------------------------------------------------------------- *)
module Iring : Rnorm = Make(Cint)
module Bring : Rnorm = Make(Cbool)

(* -------------------------------------------------------------------- *)
type c = BI.zint

let c0 : c = BI.zero
let c1 : c = BI.one

let cadd = (BI.add   : c -> c -> c)
let csub = (BI.sub   : c -> c -> c)
let cmul = (BI.mul   : c -> c -> c)
let copp = (BI.neg   : c -> c)
let ceq  = (BI.equal : c -> c -> bool)
let cdiv = (BI.ediv  : c -> c -> c * c)
