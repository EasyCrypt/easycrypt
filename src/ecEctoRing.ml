open EcRing
open EcFol
open EcTypes

exception Bad_Type
exception Bad of string


let form_to_ring (f : form) (eqs : (form * form) list) (plus : form) (minus : form) (times : form) (exp : form) (zero : form) (one : form) : pexpr * ((pexpr * pexpr) list) * (int -> form) * int=
	let c = ref 0 in
	let map = ref (fun i -> raise (Bad (string_of_int i))) in
  let ftoi = ref (fun _ -> 0) in
	let nf f d i = fun t -> (if t = d then i else f t) in
  let update t = let res = (!ftoi t) in
                  if res = 0 then (c := !c + 1; map := nf (!map) (!c) t; ftoi := nf (!ftoi) t (!c); !c)
                        else res
                                 in
	let rec ftr (f : form) : pexpr = 
		match f.f_node with
			| Fapp (op, [arg1;arg2]) when f_equal op plus -> PEadd (ftr arg1, ftr arg2)
			| Fapp (op, [arg1;arg2]) when f_equal op times -> PEmul (ftr arg1, ftr arg2)
			| Fapp (op, [arg1;arg2]) when f_equal op minus -> PEsub (ftr arg1, ftr arg2)
			| Fapp (op, arg1 :: arg2 :: []) when f_equal op exp -> (match arg2.f_node with
																		| Fint n -> PEpow (ftr arg1,n) 
																		| _ -> raise Bad_Type)
													
			| Fint n -> PEc n
			| _ when f_equal f one -> PEc 1
			| _ when f_equal f zero -> PEc 0
			| _  -> PEX (update f) in
  let newf = ftr f in
  let eqs' = List.fold_left (fun is (i,j) -> (ftr i, ftr j) :: is ) [] eqs in
	(newf,eqs',!map,!c)


let ring_to_form (f : pol) (plus : form) (minus : form) (times : form) (exp : form) (zero : form) (one : form) (map : int -> form) (gr : int) : form =
	let ty = zero.f_ty in
	let radd f1 f2 = mk_form (Fapp (plus, f1 :: f2 :: [])) ty in
	let rmul f1 f2 = mk_form (Fapp (times, f1 :: f2 :: [])) ty in
	let rsub f1 f2 = mk_form (Fapp (minus, f1 :: f2 :: [])) ty in
	let rpow f1 n = mk_form (Fapp (exp, f1 :: (mk_form (Fint n) tint) :: [])) ty in
  let rec mkIn (t : int) : form = if (t = 1) then one else radd one (mkIn (t-1)) in 
  let fint n = if (ceq n c0) then zero
               else if (ceq n c1) then one                                                                                                               
               else if (n = (-1)) then rsub zero one                                                                                                     
               else if (ty_equal ty tint) then (f_int n)                                                                                                 
               else if (n < 0) then rsub zero (mkIn (-n)) else (mkIn n) in     
  let rec rtf p c' = match p with
        | Pc c -> fint c 
        | Pinj (j,q) -> rtf q (c' - j)
        | PX (p,i,q) ->
          let xi = if i=1 then map (gr -c') else rpow (map (gr - c')) i in
          let pxi = if (peq p (Pc 1)) then xi else rmul (rtf p c') xi in         
          if (peq q (Pc 0)) then pxi else radd pxi (rtf q (c'-1)) in
   rtf f (gr - 1)

let ring_simp (f1: form) (plus : form) (minus : form) (times : form) (exp : form) (zero : form) (one : form) (eqs : (form * form) list):
	form =
	let rtf f map g = ring_to_form f plus minus times exp zero one map g in
	let (exp,eqs',map,gr) = form_to_ring f1 eqs plus minus times exp zero one in
  let nt = norm exp eqs' in
	let nf = rtf nt map gr in
	nf

let ring_eq (f1: form) (f2 : form) (plus : form) (minus : form) (times : form) (exp : form) (zero : form) (one : form) (eqs : (form * form) list) : form =
  let t = mk_form (Fapp (minus, f1 :: f2 :: [])) (zero.f_ty) in
	ring_simp t plus minus times exp zero one eqs
