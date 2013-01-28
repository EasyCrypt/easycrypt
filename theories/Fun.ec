
type ('a,'b)Fun.

op [@] : (('a,'b) Fun, 'a) -> 'b.

type 'a Pred = ('a,bool)Fun.

pred Pincl (p1:'a Pred, p2:'a Pred) = 
  forall (a:'a), p1 @ a => p2 @ a.

cnst Ptrue  : 'a Pred.
cnst Pfalse : 'a Pred.

op Peq  : 'a -> 'a Pred.
op Pnot : 'a Pred -> 'a Pred.
op Pand : ('a Pred, 'a Pred) -> 'a Pred.
op Por  : ('a Pred, 'a Pred) -> 'a Pred.

(* FIXME 
axiom Ptrue_def  : forall (x:'a), Ptrue @ x.
*) 

axiom Ptrue_def  : forall (x:'a), Ptrue @ x = true. 

axiom Pfalse_def : forall (x:'a), ! (Pfalse @ x). 

axiom Peq_def    : forall (x1:'a,x2:_), Peq(x1) @ x2 <=> (x1 = x2).

axiom Pnot_def   : forall (P:_, x:'a), Pnot(P) @ x <=> !(P @ x).

axiom Pand_def   : forall (P1:_, P2:_, x:'a), 
  Pand(P1,P2) @ x <=> ((P1 @ x) && (P2 @ x)).

axiom Por_def    : forall (P1:_, P2:_, x:'a), 
  Por(P1,P2) @ x <=> ((P1 @ x) || (P2 @ x)).







