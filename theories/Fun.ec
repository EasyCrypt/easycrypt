(** Extensional equality for functions *)
pred (==) (f g:'a -> 'b) = forall x, f x = g x.

axiom extensionality: forall (f g:'a -> 'b), f == g => f = g.

(** Computable predicates *)
type 'a cPred = 'a -> bool.

pred (<=) (p q:'a cPred) = forall (a:'a), p a => q a.

(** Operators on predicates *)
op cPtrue(x:'a) : bool = true.

op cPfalse(x:'a) : bool = false.

op cPnot(p:'a cPred, x:'a) : bool = !p x.

op cPand(p q:'a cPred, x:'a) : bool = p x /\ q x.

op cPor(p q:'a cPred, x:'a) : bool = p x \/ q x.

op cPeq(x y:'a) : bool = x = y.

(** Lemmas *)
lemma cPtrue_def : forall (x:'a), cPtrue x by []. 

lemma cPfalse_def : forall (x:'a), !cPfalse x by []. 

lemma cPnot_def : forall (p:'a cPred) x, cPnot p x <=> !p x by []. 

lemma cPand_def : 
  forall (p q:'a cPred) (x:'a), cPand p q x <=> (p x /\ q x) by [].

lemma cPor_def : 
  forall (p q:'a cPred) (x:'a), cPor p q x <=> (p x \/ q x) by [].

lemma excluded_middle: forall (p: 'a cPred),
  cPor (cPnot p) p = cPtrue
by (intros p; apply extensionality; trivial).
