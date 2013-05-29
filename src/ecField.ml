open Printf
(****** field Type  ******)
type 'a field = Plus of 'a field list (* (+ [t1,...,tn])  *)
	| Times of 'a field list
	(* | Exp of 'a field * 'a field*)
	| Minus of 'a field  (* (- t)*)
	| Inv of 'a field  (* inv(t) = 1/t  *)
	| One 
	| Zero
	| Value of 'a
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
	| (Value a, Value b) -> compare a b
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

let rec drop (n : int)  (xs : 'a list) : 'a list = match (n,xs) with
													| (0,_) -> xs
													| (_,[]) -> [] 
													| (n,y::ys) -> drop (n-1) ys
let rec rmvinvs (ts : 'a field list) : 'a field list =
  let (invs,noinvs) = List.fold_left (fun (is,ns) i ->
										match i with
											| Inv _ -> (i :: is,ns)
											| _ -> (is,i::ns)
									) ([],[]) ts in
  let rec removing (is,ns) =
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
							if (exslen < ixslen) then (drop exslen ixs) @ res else
										(drop ixslen exs) @ res 
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

let rec nprint (t : string field) =
	(match t with
		| One ->  print_string "1"
		| Zero -> print_string "0"
		| Value t -> print_string t
		| Plus xs -> print_string "(+, ";List.iter (fun i -> nprint i; print_string " ") xs; print_string ")"
		| Times xs -> print_string "(*, ";List.iter (fun i -> nprint i; print_string " ") xs; print_string ")"
		| Minus t -> print_string "-("; nprint t; print_string ")"
		| Inv t -> print_string "inv("; nprint t; print_string ")")

	
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
					match ss with
						| [] -> Zero
						| [x] -> x
						| _ -> Plus ss
		) in (!poblg,norm term)
