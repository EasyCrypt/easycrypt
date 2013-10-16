(* Pervasive.unit *)
type unit0 = unit
  
(* Pervasive.tt *)
let tt : unit0 = ()
  
(* Pervasive.int *)
type int0 = int (* DANGEROUS *)
  
(* Pervasive.real *)
type real = float (* FIXME *)
    
(* Pervasive.bool *)
type bool0 = bool
  
(* Pervasive.true *)
let true0 : bool0 = true
  
(* Pervasive.false *)
let false0 : bool0 = false
  
(* Pervasive.[!] *)
let lbexrb : bool0 -> bool0 = Pervasives.not
  
(* Pervasive./\ *)
let slbs : bool0 -> bool0 -> bool0 = Pervasives.(&&)
  
(* Pervasive.&& *)
let etet : bool0 -> bool0 -> bool0 = Pervasives.(&&)
  
(* Pervasive.\/ *)
let bssl : bool0 -> bool0 -> bool0 = Pervasives.(||)
  
(* Pervasive.|| *)
let brbr : bool0 -> bool0 -> bool0 = Pervasives.(||)
  
(* Pervasive.=> *)
let eqgt : bool0 -> bool0 -> bool0 =
  fun b1 b2 -> not b1 || b2 
  
(* Pervasive.<=> *)
let lseqgt : bool0 -> bool0 -> bool0 = Pervasives.(==)
  
(* Pervasive.= *)
let eq : 'a -> 'a -> bool0 = Pervasives.(=)

(* Pervasive.distr *)
type 'ta distr = unit -> 'ta
  
(* Pervasive.mu *)
let mu : 'ta distr -> ('ta -> bool0) -> real =
  fun d f -> assert false 



