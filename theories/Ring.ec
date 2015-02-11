(* --------------------------------------------------------------------
 * Copyright (c) - 2012-2015 - IMDEA Software Institute and INRIA
 * Distributed under the terms of the CeCILL-C license
 * -------------------------------------------------------------------- *)

pragma +implicits.

(* -------------------------------------------------------------------- *)
require import Fun.
require import Int.

(* -------------------------------------------------------------------- *)
(* FIXME: TO BE MOVED                                                   *)
theory IterOp.
  op iter ['a] : int -> ('a -> 'a) -> 'a -> 'a.

  axiom iter0 ['a] n opr (x : 'a): n <= 0 => iter n opr x = x.
  axiom iterS ['a] n opr (x : 'a): 0 <= n => iter (n+1) opr x = opr (iter n opr x).

  op iteri ['a] : int -> (int -> 'a -> 'a) -> 'a -> 'a.

  axiom iteri0 ['a] n opr (x : 'a): n <= 0 => iteri n opr x  = x.
  axiom iteriS ['a] n opr (x : 'a): 0 <= n => iteri (n+1) opr x = opr n (iteri n opr x).

  op iterop ['a] (n : int) opr (x z : 'a) : 'a =
    let f = fun i y, if i <= 0 then x else opr x y in
    iteri n f z.

  lemma iterop0 ['a] (n : int) opr (x z : 'a): n <= 0 =>
    iterop n opr x z = z.
  proof. by move=> le0_n; rewrite /iterop /= iteri0. qed.

  lemma iterop1 ['a] opr (x z : 'a): iterop 1 opr x z = x.
  proof. by rewrite /iterop /= (iteriS 0). qed.

  lemma iteropS ['a] (n : int) opr (x z : 'a): 0 <= n =>
    iterop (n+1) opr x z = iter n (opr x) x.
  proof.
    rewrite /iterop; elim n=> /=.
    + by rewrite iter0 // (iteriS 0).
    + move=> i ge0_i ih; rewrite iteriS 1:smt /= ih.
      by rewrite -(iterS _ (opr x)) //; cut ->: ! (i+1 <= 0) by smt.
  qed.
end IterOp.

import IterOp.

(* -------------------------------------------------------------------- *)
abstract theory ZModule.
  type t.

  op zeror : t.
  op ( + ) : t -> t -> t.
  op [ - ] : t -> t.

  axiom addrA: forall (x y z : t), x + (y + z) = (x + y) + z.
  axiom addrC: forall (x y   : t), x + y = y + x.
  axiom add0r: forall (x     : t), zeror + x = x.
  axiom addNr: forall (x     : t), (-x) + x = zeror.

  op ( - ) (x y : t) = x + -y axiomatized by subrE.

  lemma nosmt addr0 (x : t): x + zeror = x.
  proof. by rewrite addrC add0r. qed.

  lemma nosmt addrN (x : t): x + (-x) = zeror.
  proof. by rewrite addrC addNr. qed.

  lemma nosmt addrCA (x y z : t):
    x + (y + z) = y + (x + z).
  proof. by rewrite !addrA (addrC x y). qed.

  lemma nosmt addrAC (x y z : t):
    (x + y) + z = (x + z) + y.
  proof. by rewrite -!addrA (addrC y z). qed.

  lemma nosmt subrr (x : t): x - x = zeror.
  proof. by rewrite subrE /= addrN. qed.

  lemma nosmt addKr (x y : t): -x + (x + y) = y.
  proof. by rewrite addrA addNr add0r. qed.

  lemma nosmt addNKr (x y : t): x + (-x + y) = y.
  proof. by rewrite addrA addrN add0r. qed.

  lemma nosmt addrK (y x : t): (x + y) + -y = x.
  proof. by rewrite -addrA addrN addr0. qed.

  lemma nosmt addrNK (x y : t): (x + -y) + y = x.
  proof. by rewrite -addrA addNr addr0. qed.

  lemma nosmt addrI (x y z : t): x + y = x + z => y = z.
  proof. by move=> h; rewrite -(addKr x z) -h addKr. qed.

  lemma nosmt addIr (x y z : t): y + x = z + x => y = z.
  proof. by move=> h; rewrite -(addrK x z) -h addrK. qed.

  lemma nosmt opprK (x : t): -(-x) = x.
  proof. by apply @(addIr (-x)); rewrite addNr addrN. qed.

  lemma nosmt oppr0: -zeror = zeror.
  proof. by rewrite -(addr0 (-zeror)) addNr. qed.

  lemma nosmt subr0 (x : t): x - zeror = x.
  proof. by rewrite subrE /= oppr0 addr0. qed.

  lemma nosmt sub0r (x : t): zeror - x = - x.
  proof. by rewrite subrE /= add0r. qed.

  lemma nosmt opprD (x y : t): -(x + y) = -x + -y.
  proof. by apply @(addrI (x + y)); rewrite addrA addrN addrAC addrK addrN. qed.

  lemma nosmt opprB (x y : t): -(x - y) = y - x.
  proof. by rewrite subrE /= opprD opprK addrC. qed.

  lemma nosmt subr_eq (x y z : t):
    (x - z = y) <=> (x = y + z).
  proof.
    move: (can2_eq (fun x, x - z) (fun x, x + z) _ _ x y) => //=.
    by move=> {x} x /=; rewrite subrE /= addrNK.
    by move=> {x} x /=; rewrite subrE /= addrK.
  qed.

  lemma nosmt subr_eq0 (x y : t): (x - y = zeror) <=> (x = y).
  proof. by rewrite subr_eq add0r. qed.

  lemma nosmt addr_eq0 (x y : t): (x + y = zeror) <=> (x = -y).
  proof. by rewrite -(subr_eq0 x) subrE /= opprK. qed.

  lemma nosmt eqr_opp (x y : t): (- x = - y) <=> (x = y).
  proof.
    move: (can_eq (fun (z : t), -z) (fun (z : t), -z) _ x y) => //=.
    by move=> z /=; rewrite opprK.
  qed.

  op intmul (x : t) (n : int) =
    if n < 0
    then -(iterop (-n) ZModule.(+) x zeror)
    else  (iterop   n  ZModule.(+) x zeror).

  lemma intmul0 (x : t): intmul x 0 = zeror.
  proof. by rewrite /intmul /= iterop0. qed.

  lemma intmul1 (x : t): intmul x 1 = x.
  proof. by rewrite /intmul /= iterop1. qed.

  lemma intmulN (x : t) (n : int): intmul x (-n) = -(intmul x n).
  proof. by rewrite /intmul; case (n < 0); smt. qed.

  lemma intmulS (x : t) (n : int): 0 <= n =>
    intmul x (n+1) = x + intmul x n.
  proof. by move=> ge0_n; rewrite /intmul; smt. qed.
end ZModule.

(* -------------------------------------------------------------------- *)
clone ZModule as IntZMod with
  type t <- int,
  op   zeror <- 0,
  op   (+)   <- Int.( + ),
  op   [-]   <- Int.([-]),
  op   (-)   <- Int.( - )
  proof *.

realize addrA. by smt. qed.
realize addrC. by smt. qed.
realize add0r. by smt. qed.
realize addNr. by smt. qed.
realize subrE. by do 2! (apply/ExtEq.fun_ext=> _); smt. qed.

(* -------------------------------------------------------------------- *)
theory abstract ComRing.
  type t.

  clone export ZModule with type t <- t.

  op oner  : t.
  op ( * ) : t -> t -> t.

  axiom oner_neq0 : oner <> zeror.
  axiom mulrA     : forall (x y z : t), x * (y * z) = (x * y) * z.
  axiom mulrC     : forall (x y   : t), x * y = y * x.
  axiom mul1r     : forall (x     : t), oner * x = x.
  axiom mulrDl    : forall (x y z : t), (x + y) * z = (x * z) + (y * z).

  lemma nosmt mulr1 (x : t): x * oner = x.
  proof. by rewrite mulrC mul1r. qed.

  lemma nosmt mulrDr (x y z : t):
    x * (y + z) = x * y + x * z.
  proof. by rewrite mulrC mulrDl !(mulrC _ x). qed.

  op ofint n = intmul oner n.

  lemma ofint0: ofint 0 = zeror.
  proof. by apply/intmul0. qed.

  lemma ofint1: ofint 1 = oner.
  proof. by apply/intmul1. qed.

  lemma ofintS (i : int): 0 <= i => ofint (i+1) = oner + ofint i.
  proof. by apply/intmulS. qed.

  lemma ofintN (i : int): ofint (-i) = - (ofint i).
  proof. by apply/intmulN. qed.
end ComRing.

(* -------------------------------------------------------------------- *)
theory abstract BoolRing.
  type t.

  clone export ComRing with type t <- t.

  axiom mulrr : forall (x : t), x * x = x.

  lemma nosmt addrK (x : t): x + x = zeror.
  proof.
    apply @(addrI (x + x)); rewrite addr0 -{1 2 3 4}mulrr.
    by rewrite -mulrDr -mulrDl mulrr.
  qed.
end BoolRing.

(* -------------------------------------------------------------------- *)
theory abstract IDomain.
  type t.

  clone export ComRing with type t <- t.

  axiom mulf_eq0:
    forall (x y : t), x * y = zeror <=> x = zeror \/ y = zeror.

  lemma mulf_neq0 (x y : t): x <> zeror => y <> zeror => x * y <> zeror.
  proof. by move=> nz_x nz_y; apply/not_def; rewrite mulf_eq0; smt. qed.
end IDomain.

(* -------------------------------------------------------------------- *)
theory abstract Field.
  type t.

  clone export IDomain with type t <- t.

  op inv: t -> t.

  axiom invf0: inv zeror = zeror.
  axiom mulVf: forall (x : t), x <> zeror => (inv x) * x = oner.

  lemma mulfV (x : t): x <> zeror => x * (inv x) = oner.
  proof. by move=> /mulVf <-; rewrite mulrC. qed.

  op ( / ) (x y : t) = x * (inv y) axiomatized by divrE.

  lemma nosmt divrr (x : t): x <> zeror => x / x = oner.
  proof. by move=> nz_x; rewrite divrE /= mulfV. qed.

  lemma nosmt mulKr (x : t): x <> zeror => forall y, (inv x) * (x * y) = y.
  proof. by move=> nz_y y; rewrite mulrA mulVf // mul1r. qed.

  lemma nosmt mulrK (y : t): y <> zeror => forall x, (x * y) * (inv y) = x.
  proof. by move=> nz_y x; rewrite -mulrA mulfV // mulr1. qed.

  lemma nosmt mulVKr (x : t): x <> zeror => forall y, x * ((inv x) * y) = y.
  proof. by move=> nz_x y; rewrite mulrA mulfV // mul1r. qed.

  lemma nosmt mulrVK (y : t): y <> zeror => forall x, (x * (inv y)) * y = x.
  proof. by move=> nz_y x; rewrite -mulrA mulVf // mulr1. qed.

  lemma nosmt mulrI (x: t): x <> zeror => forall y z, x * y = x * z => y = z.
  proof.                        (* FIXME *)
    move=> nz_x y z;
      apply @(can_inj (fun (y : t), x * y) (fun (y : t), inv x * y) _ y z);
      apply @(mulKr _ nz_x).
  qed.

  axiom invK (x : t): inv (inv x) = x.

  op exp (x : t) (n : int) =
    if n < 0
    then inv (iterop (-n) IDomain.ComRing.( * ) x oner)
    else iterop n IDomain.ComRing.( * ) x oner.

  lemma expr0 x: exp x 0 = oner.
  proof. by rewrite /exp /= iterop0. qed.

  lemma expr1 x: exp x 1 = x.
  proof. by rewrite /exp /= iterop1. qed.

  lemma exprS (x : t) i: 0 <= i => exp x (i+1) = x * (exp x i).
  proof.                        (* FIXME *)
    move=> ge0_i; rewrite /exp /=.
    cut -> /=: i   < 0 = false by smt.
    cut -> /=: i+1 < 0 = false by smt.
    smt.
  qed.

  lemma exprN (x : t) (i : int): exp x (-i) = inv (exp x i).
  proof. by rewrite /exp /= IntZMod.opprK (fun_if inv) invK; smt. qed.
end Field.

(* --------------------------------------------------------------------- *)
(* Rewrite database for algebra tactic                                   *)

hint rewrite rw_algebra  : .
hint rewrite inj_algebra : .
