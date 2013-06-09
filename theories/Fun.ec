(** Extentional Equality for Functions *)
pred (==)(f1:'a -> 'b, f2:'a -> 'b) =
  forall x, f1 x = f2 x.

axiom extensionality: forall (f1 f2:'a -> 'b),
  f1 == f2 => f1 = f2.

(** Computable predicates *)
type 'a cPred = 'a -> bool.

pred cPincl(p1:'a cPred, p2:'a cPred) = 
  forall (a:'a), p1 a => p2 a.

(* Operators on Predicates *)
op cPtrue(x:'a): bool = true.
op cPfalse(x:'a): bool = false.
op cPnot(p:'a cPred, a): bool = !p a.
op cPand(p1:'a cPred, p2:'a cPred, a): bool = p1 a /\ p2 a.
op cPor(p1:'a cPred, p2:'a cPred, a): bool = p1 a \/ p2 a.

op cPeq(x1:'a,x2): bool = x1 = x2.

(* Lemmas/Redefinitions *)
lemma cPtrue_def: forall (x:'a), cPtrue x. 
lemma cPfalse_def: forall (x:'a), !cPfalse x. 
lemma cPnot_def: forall (P:'a cPred) x, cPnot P x <=> !P x. 
lemma cPand_def: forall P1 P2 (x:'a), 
  cPand P1 P2 x <=> (P1 x /\ P2 x).
lemma cPor_def: forall P1 P2 (x:'a), 
  cPor P1 P2 x <=> (P1 x \/ P2 x).
