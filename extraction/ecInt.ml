  
(* Int.- *)
let mn = (-)
  
(* Int.* *)
let aas = ( * )
  
(* Int.[-] *)
let lbmnrb = (~-)
  
(* Int.+ *)
let pl = (+)
  
(* Int.<= *)
let lseq (x:int) (y:int) = x <= y

(* Int.>= *)
let gteq (x:int) (y:int) = x >= y
  
(* Int.> *)
let gt (x:int) (y:int) = x > y

(* Int.< *)
let ls (x:int) (y:int) = x < y
  
(* Int.one *)
let one = 1

(* Int.zero *)
let zero = 0

(* Int.Power *)
module Power = struct

  (* Int.Power.^ *)
  let rec cf x p = 
    if p <= 0 then 1 
    else 
      let pow = cf x (p lsl 1) in
      if p land 1 = 0 then pow else pow * x
  
end
  
  (* Int.EuclDiv *)
module EuclDiv = struct

  (* Int.EuclDiv.%% *)
  let pcpc = (mod)
    
  (* Int.EuclDiv./% *)
  let slpc = (/)
  
end
  
  
(* Int.Extrema *)
module Extrema = struct

  (* Int.Extrema.max *)
  let max = fun a b -> (if ls a b then b else a)
    
  (* Int.Extrema.min *)
  let min = fun a b -> (if ls a b then a else b)
  
end
  
(* Int.Abs *)
module Abs = struct

  (* Int.Abs.`|_| *)
  let bqbr_br = Pervasives.abs
  
end

