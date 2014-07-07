(* Int.zero *)
let zero : int = 0
  
(* Int.one *)
let one : int = 1
  
(* Int.< *)
let ls (x:int) (y:int) = x < y

(* Int.> *)
let gt (x:int) (y:int) = x > y
  
(* Int.<= *)
let lseq (x:int) (y:int) = x <= y
 
(* Int.>= *)
let gteq (x:int) (y:int) = x >= y
 
(* Int.+ *)
let pl = (+)

(* Int.[-] *)
let lbmnrb = (~-)
  
(* Int.* *)
let as0 = ( * )

(* Int.- *)
let mn = (-)

(* Int.Abs *)
module Abs = struct
  
  (* Int.Abs.`|_| *)
  let bqbr_br = Pervasives.abs
  
end
  
(* Int.Extrema *)
module Extrema = struct

  (* Int.Extrema.min *)
  let min = fun a b -> (if ls a b then a else b)
  
  (* Int.Extrema.max *)
  let max = fun a b -> (if ls a b then b else a)
    
end
  
(* Int.EuclDiv *)
module EuclDiv = struct

  (* Int.EuclDiv./% *)
  let slpc = (/)  

  (* Int.EuclDiv.%% *)
  let pcpc = (mod)
  
end
  
(* Int.Power *)
module Power = struct
  
  (* Int.Power.^ *)
  let rec cf x p = 
    if p <= 0 then 1 
    else 
      let pow = cf x (p lsr 1) in
      if p land 1 = 0 then pow else pow * x
        
end

(* Int.ForLoop *)
module ForLoop = struct

  (* Int.ForLoop.range *)
  let range i j st f =
    let st = ref st in
    for k = i to (j - 1) do
      st := f k !st;
    done;
    !st
end
