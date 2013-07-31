open EcField
open EcFol
open EcTypes
open EcEctoRing
open EcRing

exception Bad_Type
exception Bad of string

let form_to_field (f : form) (eqs : (form * form) list) (plus : form) (minus : form) (times : form) (inv : form) (exp : form) (div : form) (zero : form) (one : form) : fexpr * ((fexpr * fexpr) list) * (int -> form)  * int =
	let c = ref 0 in
	let map = ref (fun i -> raise (Bad (string_of_int i))) in
  let ftoi = ref (fun _ -> 0) in
	let nf f d i = fun t -> (if t = d then i else f t) in
  let update t = let res = (!ftoi t) in
                  if res = 0 then (c := !c + 1; map := nf (!map) (!c) t; ftoi := nf (!ftoi) t (!c); !c)
                        else res
                                 in
  let rec mff (t : form) : fexpr =
		match t.f_node with
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op plus  -> FEadd (mff arg1, mff arg2)
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op times -> FEmul (mff arg1, mff arg2)
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op minus -> FEsub (mff arg1, mff arg2)
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op div   -> FEdiv (mff arg1, mff arg2)
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op exp   ->
         (match arg2.f_node with
				  | (Fint n) -> FEpow (mff arg1,n) 
					| _        -> raise Bad_Type)
			| Fapp (op, arg :: []) when f_equal op inv-> FEinv (mff arg)
			| Fint n -> FEc (Big_int.big_int_of_int n)
      | _ when f_equal t one  -> FEc c1
      | _ when f_equal t zero -> FEc c0
			| _                     -> FEX (update t) in
  let eqs' = List.fold_left (fun is (i,j) -> (mff i, mff j) :: is ) [] eqs in
	(mff f,eqs',!map,!c)


let appfield ((form1,form2) :form * form) (plus : form) (minus : form) (times : form) (inv : form) (exp : form) (div : form) (zero : form) (one : form) (eqs : (form * form) list) : (form list * (form * form) * (form * form)) =
	let mff t = form_to_field t eqs plus minus times inv exp div zero one in
	let rtf f map g = ring_to_form f plus minus times exp zero one map g in

  let (e1,eqs1',map1,c) = mff form1 in
  let (num1,denum1,condition1) = fnorm e1 in

  let (e2,eqs2',map2,c2) = mff form2 in
  let (num2,denum2,condition2) = fnorm e2 in

  let es1 = List.fold_left (fun is (i,j) -> match (fnorm i, fnorm j) with
                                          | ((n,PEc l,[]),(m,PEc r, [])) when (ceq l c1 && ceq r c1) -> (n,m) :: is
                                          | _ -> raise (Bad "Hypothesis have to be a mon = pol??")) [] eqs1' in
  let es2 = List.fold_left (fun is (i,j) -> match (fnorm i,fnorm j) with
                                          | ((n,PEc l,[]),(m,PEc r,[]))  when (ceq l c1 && ceq r c1) -> (n,m) :: is
                                          | _ -> raise (Bad "Hypothesis have to be a mon = pol??")) [] eqs2' in
                                          (***)
  let num1   = rtf (norm num1 es1) map1 c in
  let num2   = rtf (norm num2 es2) map2 c2 in
  let nums   = (num1 , num2) in 
                                          (***)
  let denums = (rtf (norm denum1 es1) map1 c, rtf (norm denum2 es2) map2 c2) in 
  let cond1 = List.fold_left (fun is i -> (rtf (norm i es1) map1 c) :: is) [] condition1 in
  let cond2 = List.fold_left (fun is i -> (rtf (norm i es2) map2 c2) :: is) [] condition2 in
  let conds = cond1 @ cond2 in
  (conds, nums ,denums)

let appfield_simp (f : form) (plus : form) (minus : form) (times : form) (inv : form) (exp : form) (div : form) (zero : form) (one : form) (eqs : (form * form) list) = 
	let rtf f map g = ring_to_form f plus minus times exp zero one map g in
  let (e,eqs',map,c) = form_to_field f eqs plus minus times inv exp div zero one in
  let es = List.fold_left (fun is (i,j) -> match (fnorm i, fnorm j) with
                                          | ((n,PEc l,[]),(m,PEc r, [])) when (ceq l c1 && ceq r c1) -> (n,m) :: is
                                          | _ -> raise (Bad "Hypothesis have to be a mon = pol???")) [] eqs' in
  let (num,denum,condition) = fnorm e in
  let rn = rtf (norm num es) map c in
  let rd = rtf (norm denum es) map c in
  let cond = List.fold_left (fun is i -> (rtf (norm i es) map c) :: is) [] condition in
  (cond,rn,rd)
  
