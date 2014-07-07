(* Pervasive.unit *)
type unit0 = unit
  
(* Pervasive.tt *)
let tt : unit = ()

(* Pervasive.bool *)
type bool0 = bool
  
(* Pervasive.true *)
let true0 : bool = true
  
(* Pervasive.false *)
let false0 : bool = false
  
(* Pervasive.int *)
type int0 = int (* DANGEROUS *)
  
(* Pervasive.real *)
type real = float (* FIXME *)

(* Pervasive.= *)
let eq : 'a -> 'a -> bool = Pervasives.(=)
  
(* Pervasive.[!] *)
let lbexrb : bool -> bool = Pervasives.not
  
(* Pervasive./\ *)
let slbs : bool -> bool -> bool = Pervasives.(&&)
  
(* Pervasive.&& *)
let etet : bool -> bool -> bool = Pervasives.(&&)
  
(* Pervasive.\/ *)
let bssl : bool -> bool -> bool = Pervasives.(||)
  
(* Pervasive.|| *)
let brbr : bool -> bool -> bool = Pervasives.(||)
  
(* Pervasive.=> *)
let eqgt : bool -> bool -> bool =
  fun b1 b2 -> not b1 || b2 
  
(* Pervasive.<=> *)
let lseqgt : bool -> bool -> bool = Pervasives.(==)
  
(* Pervasive.distr *)
type 'ta distr = unit -> 'ta
  
(* Pervasive.mu *)
let mu : 'ta distr -> ('ta -> bool) -> real =
  fun d f -> assert false 



