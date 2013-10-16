(* Pair.fst *)
let fst (p : 'a * 'b) =
  let (a, b) = p in a
  
(* Pair.snd *)
let snd (p : 'a * 'b) =
  let (a, b) = p in b
  
(* Pair.Dprod *)
module Dprod = struct
  
    (* Pair.Dprod.* *)
  let as0 (d1 : 'a EcPervasive.distr) (d2 : 'b EcPervasive.distr) :
      ('a * 'b) EcPervasive.distr =
    fun _ -> (d1 (), d2 ())

end
