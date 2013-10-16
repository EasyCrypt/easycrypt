(* Pair.fst *)
let fst = Pervasives.fst 

(* Pair.snd *)
let snd = Pervasives.snd 

(* Pair.Dprod *)
module Dprod = struct

  (* Pair.Dprod.* *)
  let aas (d1 : 'a EcPervasive.distr) (d2: 'a EcPervasive.distr) : 
                ('a * 'b) EcPervasive.distr = 
    fun _ -> (d1 (), d2 ())
  
end
