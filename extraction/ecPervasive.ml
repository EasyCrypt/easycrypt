(* Pervasive *)
type tunit = unit
type unit = tunit
(* Pervasive.tt *)
let tt :  unit = ()

(* Pervasive.bool *)
type tbool = bool
type bool = tbool 

(* Pervasive.false *)
let _false : bool = false 
  
(* Pervasive.true *)
let _true : bool = true

(* Pervasive.<=> *)
let lseqgt : ( bool -> ( bool ->  bool)) = Pervasives.(==)
  
(* Pervasive.=> *)
let eqgt b1 b2 = not b1 || b2 
  
(* Pervasive.|| *)
let brbr = Pervasives.(||)
  
(* Pervasive.\/ *)
let bssl = Pervasives.(||)
  
(* Pervasive.&& *)
let etet = Pervasives.(&&)
  
(* Pervasive./\ *)
let slbs = Pervasives.(&&)
  
(* Pervasive.[!] *)
let lbexrb = Pervasives.not

(* DANGEROUS *)
type tint = int
type int = tint

(* Pervasive.real *)
type real = float (* FIXME *)

(* Pervasive.distr *)
type 'ta distr = unit -> 'ta
  
(* Pervasive.mu *)
let mu : ('ta distr -> (('ta ->  bool) ->  real)) =
  fun d f -> assert false 
 
(* Pervasive.= *)
let eq : ('a -> ('a ->  bool)) = Pervasives.(=)
    

