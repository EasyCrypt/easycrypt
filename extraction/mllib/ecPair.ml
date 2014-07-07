(* Pair.fst *)
let fst (p : 'a * 'b) =
  let (a0, b0) = p in a0
  
(* Pair.snd *)
let snd (p : 'a * 'b) =
  let (a0, b0) = p in b0
  
(* Pair.Dprod *)
module Dprod = struct
  
    (* Pair.Dprod.* *)
  let as0 (d1 : 'a EcPervasive.distr) (d2 : 'b EcPervasive.distr) :
      ('a * 'b) EcPervasive.distr =
    fun _ -> (d1 (), d2 ())

end
