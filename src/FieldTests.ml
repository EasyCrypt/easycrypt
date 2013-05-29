open EcField

let a = Value "a"
let b = Value "b"
let c = Value "c"
let d = Value "d"

(***)
let prod p q = Times (p :: q :: [])
let sum p q = Plus (p :: q :: [])
let inv p = Inv p
let minus p = Minus p
(***)
let mostrar a = let (ps,a') = field_norm a in
				print_string "Term:"; nprint a; print_string " -->> "; nprint a';print_string "\nProofs:\n";
				List.iter (fun i -> nprint i; print_string " ") ps; print_string "\n"

(* binomio (a*b * (a*b) = a*a + a * b + b * a + b * b)*)
let t1 = prod (sum a b) (sum a b)
let _ = mostrar t1
(* a -a = 0*)
let t2 = sum a (minus a)
let _ = mostrar t2
(*a * inv a = 1*)
let t3 = prod a (inv a)
let _ = mostrar t3
(* Test1  *)
(* (a * (c*s + r) + c*d - c*(a*s + b*r + d)) * (inv (a - b*c)) *)
let r = Value "r"
let s = Value "s"
let tt1 = sum (prod c s) r
let tt2 = prod a tt1
let tt3 = prod c d
let tt4 = Plus ((prod a s) :: prod b r :: d :: [])
let tt5 = prod c tt4
let t4 = Plus (tt2 :: tt3 :: minus tt5 :: [] )
let tt6 = sum a (minus (prod b c))
let t5 = inv tt6
let t6 = prod t4 t5
let _ = mostrar t4
let _ = mostrar t5
let _ = mostrar t6
