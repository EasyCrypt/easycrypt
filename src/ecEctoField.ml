open EcField
open EcFol
open EcTypes
exception Think

let rec badrep (x : int) : 'a field list = match x with
									| 0 -> [] 
									| n -> One :: (badrep (n-1))

let form_to_field (f : form) (plus : form) (minus : form) (times : form) (inv : form) (zero : form) (one : form) : ty field =
	let rec mff (t : form) : ty field =
			if f_equal t zero then Zero else
			if f_equal t one then One else
			(match t.f_node with
				| Fapp (op, args) when f_equal op plus -> Plus (List.fold_left (fun is i -> (mff i) :: is) [] args )
				| Fapp (op, args) when f_equal op times -> Times (List.fold_left (fun is i -> (mff i) :: is) [] args )
				| Fapp (op, arg :: []) when f_equal op inv-> Inv (mff arg)
				| Fapp (op, arg :: []) when f_equal op minus -> Minus (mff arg)
				| Fapp (op, args) -> Op (t.f_ty,op,(List.map mff args))
				| Fint 0 -> Zero
				| Fint 1 -> One
				| Fint i -> Plus (badrep i)  (*Value t  replace by 1+1+1+1+1+1++1+1+1+1... *)
				| Flocal _ -> Value t
				| Fpvar _ -> Value t
				| Fglob _ -> Value t
				| _ -> raise Think)
	in mff f
let field_to_form (f : ty field) (plus : form) (minus : form) (times : form) (inv : form) (zero : form) (one : form) : form =
	let ty = zero.f_ty in
	let rec ffm ( f : ty field) : form =
		match f with
			| Zero -> zero
			| One -> one
			| Value t -> t
			| Op (ty',op,args) -> mk_form (Fapp (op, List.map ffm args)) ty'
			| Plus xs -> mk_form (Fapp (plus, List.map ffm xs)) ty
			| Times xs -> mk_form (Fapp (times, List.map ffm xs)) ty
			| Inv x -> mk_form (Fapp (inv, ffm x :: [])) ty
			| Minus x -> mk_form (Fapp (minus, ffm x :: [])) ty
	in ffm f

let rec rmvrep ts = match ts with
					| [] -> []
					| x :: xs -> x :: ( rmvrep (List.fold_left (fun is i -> if (f_equal x i) then is else (i::is)) [] xs) )

let appfield ((form1,form2) :form * form) (plus : form) (minus : form) (times : form) (inv : form) (zero : form) (one : form) 
	: (form list * (form * form) list) =
	let mff t = form_to_field t plus minus times inv zero one in
	let ffm t = field_to_form t plus minus times inv zero one in
	let (zs,obs) = eqfield (mff form1) (mff form2) in
	let fzs = rmvrep (List.fold_left (fun is l ->  (ffm l) :: is) [] zs) in
	let fobs = List.fold_left (fun is (l,r) -> (ffm l, ffm r) :: is) [] obs in
	(fzs,fobs)

let appfield_simp (f : form) (plus : form) (minus : form) (times : form) (inv : form) (zero : form) (one : form)  
	: (form list * form) =
	let mff t = form_to_field t plus minus times inv zero one in
	let ffm t = field_to_form t plus minus times inv zero one in
	let (zs,res) = field_norm (mff f) in
	let fzs = rmvrep (List.fold_left (fun is l ->  (ffm l) :: is) [] zs) in
	(fzs, ffm res)

