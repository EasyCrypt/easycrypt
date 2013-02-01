axiom f_extentionality : 
  forall (f1: 'a -> 'b, f2 : 'a -> 'b),
     (forall (x:'a), f1(x) = f2(x)) =>
     f1 = f2.

type 'a Pred = 'a -> bool.

pred Pincl (p1:'a Pred, p2:'a Pred) = 
  forall (a:'a), p1(a) => p2(a).

op Ptrue (x:'a) : bool = true.

op Pfalse (x:'a) : bool = false.

op Pnot (p:'a Pred, a:'a) : bool = !p(a).
op Pand (p1: 'a Pred, p2: 'a Pred, a:'a) : bool = p1(a) && p2(a).
op Por  (p1: 'a Pred, p2: 'a Pred, a:'a) : bool = p1(a) || p2(a).

op Peq (x1:'a,x2:'a) : bool = x1 = x2.

axiom Ptrue_def  : forall (x:'a), Ptrue(x). 

axiom Pfalse_def : forall (x:'a), ! Pfalse(x). 

axiom Pnot_def   : forall (P:'a Pred, x:'a), (Pnot(P, x)) <=> (!P(x)). 

axiom Pand_def   : forall (P1:_, P2:_, x:'a), 
  Pand(P1,P2,x) <=> (P1(x) && P2(x)).

axiom Por_def    : forall (P1:_, P2:_, x:'a), 
  Por(P1,P2,x) <=> (P1(x) || P2(x)).







