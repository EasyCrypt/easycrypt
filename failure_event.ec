require import RandOrcl.
require import Array.
require import Bitstring.
require import Map.
require import Set.
require import ISet.
require import Int.
require import Distr.
require import Bool.
require import Real.
require import Pair.
require import Word.


op k : int. 
op l : int.

clone Word as X with op length = k.
clone Word as Y with op length = l.

type X = X.word.
type Y = Y.word.

op uniform_X : X distr = X.Dword.dword.
op uniform_Y : Y distr = Y.Dword.dword.

const qH : int.

clone RandOrcl as RandOrcle with 
type from = X, 
type to = Y,
op dsample = uniform_Y,
op qO = qH,
op default = Y.zeros.

import RandOrcle.
import ROM.
import WRO_Set.

module type Adv(O : Oracle) = {
 fun a () : unit {O.o}
}.

module M (A_ : Adv) ={
 module ARO = ARO(RO)
 module A = A_(ARO)
 var r : X
 fun main () : bool ={
  r = $uniform_X;
  ARO.init();
  A.a();
  return true;
 }

}. 

require Sum.
lemma asd :
forall(A <: Adv {M,ARO,RO}) &m,Pr[M(A).main() @ &m : mem M.r ARO.log /\ card ARO.log <= qH] <= (qH%r * 1%r / (2%r ^ k)).
proof.
 intros A &m.
 fel 2 (card ARO.log) (lambda i, 1%r / (2%r ^ k) ) qH (mem M.r ARO.log) true.
  admit. (* smt *)
  trivial.
  (* initialization of bad and counter *)
  inline M(A).ARO.init; wp; inline RO.init; wp; rnd; skip; smt.
  (* *)  

  (* bad judgements over o Oracle call *)
  fun.
  inline RO.o.

