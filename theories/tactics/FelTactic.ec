(* -------------------------------------------------------------------- *)
require import Fun Pred FSet StdBigop.
(*---*) import Bigreal.

(* -------------------------------------------------------------------- *)
op felsum (f : int -> real) (n m : int) =
  BRA.bigi predT f n m.
