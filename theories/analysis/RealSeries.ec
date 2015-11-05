(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2015 - IMDEA Software Institute
 * Copyright (c) - 2012--2015 - Inria
 * 
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Bool Option Fun Distr Int IntExtra Real RealExtra.
require import StdRing StdOrder StdBigop Discrete List RealSeq.
(*---*) import IterOp Bigreal.BAdd.

pragma +implicits.

(* -------------------------------------------------------------------- *)
op partial (s : int -> real) (n : int) : real =
  bigi predT s 0 n.

op convergeto (s : int -> real) (x : real) =
  RealSeq.convergeto (partial s) x.

op converge (s : int -> real) =
  exists x, convergeto s x.

(* -------------------------------------------------------------------- *)
op summable (s : 'a -> real) =
  exists M, forall J,
    uniq J => big predT (fun i => `|s i|) J <= M.

axiom sbl_countable (s : 'a -> real) :
  summable s => countable (fun i => s i <> 0%r).

(* -------------------------------------------------------------------- *)
op pos (s : 'a -> real) = fun i => if s i < 0%r then 0%r else `|s i|.
op neg (s : 'a -> real) = fun i => if s i > 0%r then 0%r else `|s i|.

op sum (s : 'a -> real) =
  if summable s then
      lub (fun M => exists J, uniq J /\ M = big predT (pos s) J)
    - lub (fun M => exists J, uniq J /\ M = big predT (neg s) J)
  else 0%r.

axiom nosmt sumE (s : 'a -> real) :
  forall (J : int -> 'a option),
       (forall i j x, J i = Some x => J j = Some x => i = j)
    => (forall x, s x <> 0%r => exists i, 0 <= i /\ J i = Some x)
    => sum s = lim (fun n => big predT s (pmap J (range 0 n))).

(* -------------------------------------------------------------------- *)
lemma nosmt sumE_id (s : int -> real) :
  sum s = lim (fun n => big predT s (range 0 n)).
proof. admit. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt sumE_fin ['a] (s : 'a -> real) (J : 'a list) :
     uniq J
  => (forall x, s x <> 0%r => mem J x)
  => sum s = big predT s J.
proof. admit. qed.
