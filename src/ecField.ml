open Printf
open EcFol
(****** field Type  ******)
type 'a field = Plus of 'a field list (* (+ [t1,...,tn])  *)
	| Times of 'a field list
	(* | Exp of form field * form field*)
	| Minus of 'a field  (* (- t)*)
	| Inv of 'a field  (* inv(t) = 1/t  *)
	| One 
	| Zero
	| Value of form
	| Op of 'a * form * 'a field list
(*************************)
exception Div_by_Zero
exception Err

(*************************)
(******Aux functions******)

let rec list_cmp ts ps =
	match (ts,ps) with
		|([],[]) -> 0
		|(_::_,[]) -> 1
		|([],_::_) -> -1
		| (x::xs,y::ys) -> (match cmp x y with
									| 0 -> list_cmp xs ys
									| a -> a)
and cmp (t1 : 'a field) (t2 : 'a field) : int =
	match (t1,t2) with
	| (Zero, Zero) -> 0
	| (_, Zero) -> 1
	| (Zero, _) -> -1
	| (One, One) -> 0
	| (_, One) -> 1
	| (One, _) -> -1
	| (Value a, Value b) -> f_compare a b (*  <<<--- Replace this  *)
	| (_, Value _) -> 1
	| (Value _, _) -> -1
	| (Inv a, Inv b) -> cmp a b
	| (_, Inv _) -> 1
	| (Inv _, _) -> -1
	| (Minus a, Minus b) -> cmp a b
	| (_, Minus _) -> 1
	| (Minus _, _) -> -1
	| (Plus xs, Plus ys) -> let ys' = List.fast_sort cmp ys in
							let xs' = List.fast_sort cmp xs in
							list_cmp xs' ys'
	| (_, Plus _) -> 1
	| (Plus _, _) -> -1
	| (Times xs, Times ys) -> let ys' = List.fast_sort cmp ys in
							let xs' = List.fast_sort cmp xs in
							list_cmp xs' ys'
	| (_, Times _) -> 1
	| (Times _, _) -> -1
	| (Op (_,op1, args1) , Op (_,op2,args2) ) -> (match (f_compare op1 op2) with
												| 0 -> list_cmp args1 args2 
												| a -> a)

let rec drop (n : int)  (xs : 'a list) : 'a list = match (n,xs) with
													| (0,_) -> xs
													| (_,[]) -> [] 
													| (n,_::ys) -> drop (n-1) ys
let rec rmvinvs (ts : 'a field list) : 'a field list =
  let (invs,noinvs) = List.fold_left (fun (is,ns) i ->
										match i with
											| Inv _ -> (i :: is,ns)
											| _ -> (is,i::ns)
									) ([],[]) ts in
  let rec removing ((is,ns) : 'a field list * 'a field list) : 'a field list =
		(match (is,ns) with
			| ([],_) -> ns
			| (_,[]) -> is
			| (x :: _, _) -> 
						let (exs, dxs) = List.fold_left (fun (ls,rs) i ->
														if (cmp i x) = 0 then (i::ls,rs) else (ls,i::rs)) ([],[]) is in
						let ix = (match x with
									| Inv i -> i
									| _ -> raise Err) in
						let (ixs, nixs) = List.fold_left (fun (ls,rs) i ->
														if (cmp i ix = 0) then (i::ls,rs) else (ls,i::rs)) ([],[]) ns in
						let (exslen,ixslen) = (List.length exs, List.length ixs) in (* we can compute this with the folds*)
						let res = removing(dxs,nixs) in
						if (exslen = ixslen) then res else
							(if (exslen < ixslen) then (drop exslen ixs) @ res else
										(drop ixslen exs) @ res)
			) in
	removing (invs,noinvs)

let rec rmvinvs2 (ts : 'a field list) : 'a field list =
  let (invs,noinvs) = List.fold_left (fun (is,ns) i ->
										match i with
											| Minus _ -> (i :: is,ns)
											| _ -> (is,i::ns)
									) ([],[]) ts in
  let rec removing (is,ns) =
		(match (is,ns) with
			| ([],_) -> ns
			| (_,[]) -> is
			| (x :: _, _) -> 
						let (exs, dxs) = List.fold_left (fun (ls,rs) i ->
														if (cmp i x =0) then (i::ls,rs) else (ls,i::rs)) ([],[]) is in
						let ix = (match x with
									| Minus i -> i
									| _ -> print_string "Si aca \n"; raise Err) in
						let (ixs, nixs) = List.fold_left (fun (ls,rs) i ->
														if (cmp i ix = 0) then (i::ls,rs) else (ls,i::rs)) ([],[]) ns in
						let (exslen,ixslen) = (List.length exs, List.length ixs) in (* we can compute this with the folds*)
						let res = removing(dxs,nixs) in
						if (exslen = ixslen) then res else
							if (exslen < ixslen) then (drop exslen ixs) @ res else
										(drop ixslen exs) @ res 
			) in
	removing (invs,noinvs)

let rec search (ts : 'a field list) : ('a field option * 'a field list) =
	(match ts with
		| [] -> (None, [])
		| (Plus t)::ts -> (Some (Plus t), ts)
		| t :: ts -> let (b,v) = search ts in
						(b,t::v))

	
(*************************)
(* Given a field term, return a list of different-zero proof obligations
and a new field term (with no fresh variables) but normalized *)
let field_norm (term : 'a field) : 'a field list * 'a field =
	let poblg = ref [] in
	let rec norm (t : 'a field) : 'a field =
		(match t with
			| One -> One
			| Zero -> Zero
			| Value a -> Value a
			| Minus f -> let f' = norm f in
							(match f' with
								| Zero -> Zero
								| One -> Minus f'
								| Value _ -> Minus f'
								| Plus xs -> norm (Plus (List.fold_left (fun is i -> (Minus i) :: is
													) [] xs))
								| Minus a -> a
								| _ -> Minus f'
							)
			| Inv f -> let f' = norm f in
						(match f' with
							| Zero -> raise Div_by_Zero
							| One -> One
							| Inv a -> a
							| Minus a -> norm (Minus (Inv a))
							| Times xs -> norm (Times (List.fold_left (fun is i -> (Inv i) :: is
													) [] xs))
							| _ -> poblg := f' :: !poblg ; Inv f'
						)
			| Times ts ->  
					let (p,ts') = List.fold_left (fun (p,is) i ->
													let i' = norm i in
													 (match i' with
														| Minus (Times is') -> (p+1,is' @ is)
														| Minus i'' -> (p+1, i'' :: is)
														| Times is' -> (p, is' @ is)
														| One -> (p,is)
														| _ -> (p,i' :: is))) (0,[]) ts in
					(*remove as invs as I can*)
					let ss = rmvinvs ts' in
					let (invs,noinvs) = List.fold_left (fun (is,ns) i ->
										match i with
											| Inv _ -> (i :: is,ns)
											| _ -> (is,i::ns)
									) ([],[]) ss in
					let nis = (match (invs,noinvs) with
										| ([],_) -> Times noinvs
										| (_, x :: []) -> x
										| _ -> norm (Times noinvs)) in
					let nfs = (match nis with
										| Times nis' -> invs @ nis'
										| _ -> nis :: invs) in
					let ts'' = rmvinvs nfs in
					let resultado = (match ts'' with
										| [] -> One
										| _ -> if (List.mem Zero ts'') then 
														Zero
												else
													 (match search ts'' with
														| (None, x :: []) -> x
														| (None, res) -> Times res
														| (Some sum, []) -> sum
														| (Some (Plus xs), res) ->
															let dist = List.fold_left (fun is i ->(Times (i::res)) :: is) [] xs in
															norm (Plus dist)
														| _ -> raise Err
													))
					in if (p mod 2 <> 0) then norm (Minus resultado) else resultado
			| Plus xs ->
					let ts' = List.fold_left (fun is i ->
													let i' = norm i in
													match i' with
															| Plus is' -> is' @ is 
															| Zero -> is 
															| _ -> i' :: is) [] xs in
					let ss = rmvinvs2 ts' in
					(match ss with
						| [] -> Zero
						| [x] -> x
						| _ -> Plus ss)
			| Op (a, op, args) -> Op (a, op, List.map norm args) 
		) in (!poblg,norm term)

let rec eqfield (t1 : 'a field) (t2 : 'a field) : ('a field list * ('a field * 'a field) list) = 
	match (t1,t2) with
		| (Times ts1, Times ts2) -> 
			let mts1 = List.fold_left (fun is i -> let (_,i') = field_norm i in
																match i' with
																	| Times ts -> ts @ is
																	| _ -> i' :: is) [] ts1 in
			let mts2 = List.fold_left (fun is i -> let (_,i') = field_norm i in
																match i' with
																	| Times ts -> ts @ is
																	| _ -> i' :: is) [] ts2 in
			let (i1,r1) = List.fold_left (fun (ls,rs) i -> match i with
															| Inv i' -> (i' :: ls,rs)
															| _ -> (ls,i::rs)) ([],[]) mts1 in
			let (i2,r2) = List.fold_left (fun (ls,rs) i -> match i with
															| Inv i' -> (i' :: ls,rs)
															| _ -> (ls,i::rs)) ([],[]) mts2 in
			let rem1 = match r1 with
						| [] -> One
						| x :: [] -> x
						| _ -> Times r1 in
			let rem2 = match r2 with
						| [] -> One
						| x :: [] -> x
						| _ -> Times r2 in
			(match (i1,i2) with
					| ([],[]) -> let ((o1,t1'),(o2,t2')) = (field_norm t1, field_norm t2) in
									if (cmp t1' t2' = 0) then (o1 @ o2,[]) else
												(o1 @ o2, (t1',t2'):: [])
					| (_,[]) -> let (o1,o2) = eqfield rem1 (Times (rem2 :: i1)) in
												(i1 @ o1, o2)
					| ([],_) -> let (o1,o2) = eqfield (Times (rem1 :: i2)) rem2 in
												(i2 @ o1, o2)
					| _ -> let (o1,o2) = eqfield (Times (rem1 :: i2)) (Times (rem2 :: i1)) in
												(i1 @ i2 @ o1,o2))
		| (Times ts1, _) -> 
			let mts1 = List.fold_left (fun is i -> let (_,i') = field_norm i in
																match i' with
																	| Times ts -> ts @ is
																	| _ -> i' :: is) [] ts1 in
			let (i1,r1) = List.fold_left (fun (ls,rs) i -> match i with
															| Inv i' -> (i' :: ls,rs)
															| _ -> (ls,i::rs)) ([],[]) mts1 in
			let rem1 = match r1 with
						| [] -> One
						| x :: [] -> x
						| _ -> Times r1 in
			(match i1 with
					| [] -> 
							let (o2,t2') = field_norm t2 in
							(match t2' with
								| Times _ -> let (ob1,eqt) = eqfield t1 t2' in
												(o2 @ ob1, eqt)
								| _ -> let (o1,t1') = field_norm t1 in
											if (cmp t1' t2' = 0) then (o2 @ o1,[]) else
											(o2 @ o1,(t1',t2') :: []))
					| _ -> let (o1,o2) = eqfield rem1 (Times (t2 :: i1)) in
											(i1 @ o1,o2))
		| (_, Times ts2) ->
			let mts2 = List.fold_left (fun is i -> let (_,i') = field_norm i in
																match i' with
																	| Times ts -> ts @ is
																	| _ -> i' :: is) [] ts2 in
			let (i2,r2) = List.fold_left (fun (ls,rs) i -> match i with
															| Inv i' -> (i' :: ls,rs)
															| _ -> (ls,i::rs)) ([],[]) mts2 in
			let rem2 = match r2 with
						| [] -> One
						| x :: [] -> x
						| _ -> Times r2 in
			(match i2 with
				| [] -> let (tss1,t1') = field_norm t1 in
						(match t1' with
								| Times _ -> let (ob2, eqt) =  eqfield t1' t2 in
															(tss1 @ ob2, eqt)
								| _ -> let (tss2,t2') = field_norm t2 in
									if (cmp t1' t2' = 0) then (tss1 @ tss2 ,[]) else (tss1 @ tss2,(t1',t2') :: []))
				| _ -> let (o1,o2) = eqfield (Times (t1 :: i2)) rem2  in
 													( i2 @ o1, o2))
		| (Op (a1,op1,args1) , Op (a2,op2, args2)) -> (match (f_compare op1 op2) with (* replace this...*)
														| 0 -> List.fold_left (fun (zs,pb) (l,r) -> let (z,pbs) = eqfield l r in (z @ zs,pbs @ pb)
																			) ([],[]) (List.combine args1 args2)
														| _ -> ([],(Op (a1,op1,args1) , Op (a2,op2,args2)) :: []))
		| (Plus xs, Plus ys) -> let (pbs,t') = (field_norm (Plus ((Minus (Plus xs)) :: ys))) in (*We can do a better search...*)
								let (z,pp) = eqfield t' Zero in
									(pbs @ z, pp)
		| _ -> let ((o1,t1'),(o2,t2')) = (field_norm t1, field_norm t2) in
				let obligaciones = o1 @ o2 in
				(match (t1',t2') with
						| (Times _, _) -> let (l,r) = eqfield t1' t2' in
											(l @ obligaciones, r)
						| (_, Times _) -> let (l,r) = eqfield t1' t2' in
											(l @ obligaciones, r)
						| _ -> if (cmp t1' t2' = 0) then (obligaciones, []) else (obligaciones, [(t1',t2')]))
