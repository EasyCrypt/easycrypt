(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
require import Tactics.

(* -------------------------------------------------------------------- *)
op witness : 'a.                (* All types are inhabited in EC *)

(* -------------------------------------------------------------------- *)
abbrev [-printing] fst (p : 'a * 'b): 'a = p.`1.
abbrev [-printing] snd (p : 'a * 'b): 'b = p.`2.

op ofst ['a 'b] (x : 'a * 'b) = fst x.
op osnd ['a 'b] (x : 'a * 'b) = snd x.

(* -------------------------------------------------------------------- *)
type 'a option = [None | Some of 'a].

op option_rect ['a 'b] (v : 'a) (f : 'b -> 'a) xo =
  with xo = None   => v
  with xo = Some x => f x.

op oapp ['a 'b] (f : 'a -> 'b) d ox : 'b =
  with ox = None   => d
  with ox = Some x => f x.

op odflt (d : 'a) ox =
  with ox = None   => d
  with ox = Some x => x.

op obind ['a 'b] (f : 'a -> 'b option) ox =
  with ox = None   => None
  with ox = Some x => f x.

op omap ['a 'b] (f : 'a -> 'b) ox =
  with ox = None   => None
  with ox = Some x => Some (f x).

op oget (ox : 'a option) = odflt witness<:'a> ox.

op is_none (ox : 'a option) =
  with ox = None   => true
  with ox = Some _ => false.

op is_some (ox : 'a option) =
  with ox = None   => false
  with ox = Some _ => true.

op (\c) ['a 'b 'c] (f : 'b -> 'a option) (g : 'c -> 'b option) =
  fun x => obind f (g x).

(* -------------------------------------------------------------------- *)
op idfun ['a] (x:'a) = x.

(* -------------------------------------------------------------------- *)
pred (== ) (f g : 'a -> 'b) = forall x, f x = g x.
pred (===) (f g : 'a -> 'b -> 'c) = forall x y, f x y = g x y.

(* -------------------------------------------------------------------- *)
axiom fun_ext ['a 'b] (f g:'a -> 'b): f = g <=> f == g.

lemma fun_ext2 ['a 'b 'c] (f g : 'a -> 'b -> 'c) :
  f = g <=> (forall x y, f x y = g x y).
proof.
by split=> [->//|eq]; apply/fun_ext=> x; apply/fun_ext=> y; apply/eq.
qed.

(* -------------------------------------------------------------------- *)
pred preim ['a 'b] (f : 'a -> 'b) p x = p (f x).

(* -------------------------------------------------------------------- *)
abbrev transpose ['a 'b 'c] (f : 'a -> 'b -> 'c) (y : 'b) =
  fun x => f x y.

(* -------------------------------------------------------------------- *)
op eta_ (f : 'a -> 'b) = fun x => f x
  axiomatized by etaE.

(* -------------------------------------------------------------------- *)
op (\o) ['a 'b 'c] (g : 'b -> 'c) (f : 'a -> 'b) =
  fun x => g (f x).

op (\o2) ['a 'b 'c 'd] (f : 'c -> 'd) (g : 'a -> 'b -> 'c) =
  fun a b => f (g a b).

(* -------------------------------------------------------------------- *)
pred morphism_1 (f : 'a -> 'b) aF rF =
  forall x, f (aF x) = rF (f x).

pred morphism_2 (f : 'a -> 'b) aOp rOp =
  forall x y, f (aOp x y) = rOp (f x) (f y).

pred homomorphism_1 (f : 'a -> 'b) aP rP =
  forall x, aP x => rP (f x).

pred homomorphism_2 (f : 'a -> 'b) aR rR =
  forall x y, aR x y => rR (f x) (f y).

pred monomorphism_1 (f : 'a -> 'b) (aP : 'a -> 'c) rP =
  forall x, rP (f x) = aP x.

pred monomorphism_2 (f : 'a -> 'b) (aR : 'a -> 'a -> 'c) rR =
  forall x y, rR (f x) (f y) = aR x y.

(* -------------------------------------------------------------------- *)
pred injective (f : 'a -> 'b) =
  forall x y, f x = f y => x = y.

pred surjective (f: 'a -> 'b) =
  forall x, exists y, x = f y.

pred cancel (f : 'a -> 'b) (g : 'b -> 'a) =
  forall x, g (f x) = x.

pred pcancel (f : 'a -> 'b) (g : 'b -> 'a option) =
  forall x, g (f x) = Some x.

pred ocancel (g : 'b -> 'a option) h =
  forall x, oapp h x (g x) = x.

pred bijective ['a 'b] (f : 'b -> 'a) =
  exists g, cancel f g /\ cancel g f.

pred involutive (f:'a -> 'a) = cancel f f.

(* -------------------------------------------------------------------- *)
pred left_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o (inv x) x = e.

pred right_inverse (e:'a) (inv:'a -> 'a) (o:'a -> 'a -> 'a) =
  forall (x:'a), o x (inv x) = e.

pred left_inverse_in (p : 'a -> bool) (e : 'a) inv (o : 'a -> 'a -> 'a) =
  forall x, p x => o (inv x) x = e.

pred right_inverse_in (p : 'a -> bool) (e : 'a) inv (o : 'a -> 'a -> 'a) =
  forall x, p x => o x (inv x) = e.

pred left_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o y x = o z x => y = z.

pred right_injective (o:'a -> 'a -> 'a) =
  forall (x y z:'a), o x y = o x z => y = z.

pred left_injective_in p (o:'a -> 'a -> 'a) =
  forall x, p x => forall y z, o y x = o z x => y = z.

pred right_injective_in p (o:'a -> 'a -> 'a) =
  forall x, p x => forall y z, o x y = o x z => y = z.

pred right_id e (o:'a -> 'b -> 'a) =
  forall x, o x e = x.

pred left_zero z (o:'a -> 'b -> 'a) =
  forall x, o z x = z.

pred right_commutative (o:'a -> 'b -> 'a) =
  forall x y z, o (o x y) z = o (o x z) y.

pred left_distributive (o1:'a -> 'b -> 'a) (o2:'a -> 'a -> 'a) =
  forall x y z, o1 (o2 x y) z = o2 (o1 x z) (o1 y z).

pred right_loop (inv : 'b -> 'b) (o:'a -> 'b -> 'a) =
  forall y, cancel (fun x, o x y) (fun x, o x (inv y)).

pred rev_right_loop inv (o:'a -> 'b -> 'a) =
  forall y, cancel (fun x, o x (inv y)) (fun x, o x y).

pred left_loop inv (o:'a -> 'b -> 'b) =
  forall x, cancel (o x) (o (inv x)).

pred rev_left_loop inv (o:'a -> 'b -> 'b) =
  forall x, cancel (o (inv x)) (o x).

pred right_loop_in p (inv : 'b -> 'b) (o:'a -> 'b -> 'a) =
  forall y, p y => cancel (fun x, o x y) (fun x, o x (inv y)).

pred rev_right_loop_in p inv (o:'a -> 'b -> 'a) =
  forall y, p y => cancel (fun x, o x (inv y)) (fun x, o x y).

pred left_loop_in p inv (o:'a -> 'b -> 'b) =
  forall x, p x => cancel (o x) (o (inv x)).

pred rev_left_loop_in p inv (o:'a -> 'b -> 'b) =
  forall x, p x => cancel (o (inv x)) (o x).

pred left_id e (o:'a -> 'b -> 'b) =
  forall x, o e x = x.

pred right_zero z (o:'a -> 'b -> 'b) =
  forall x, o x z = z.

pred left_commutative (o:'a -> 'b -> 'b) =
  forall x y z, o x (o y z) = o y (o x z).

pred right_distributive (o:'a -> 'b -> 'b) add =
  forall x y z, o x (add y z) = add (o x y) (o x z).

pred self_inverse e (o:'a -> 'a -> 'b) =
 forall x, o x x = e.

pred commutative (o:'a -> 'a -> 'b) =
  forall x y, o x y = o y x.

pred idempotent (o:'a -> 'a -> 'a) =
  forall x, o x x = x.

pred associative (o:'a -> 'a -> 'a) =
  forall x y z, o x (o y z) = o (o x y) z.

pred interchange op1 op2 =
  forall (x:'a) y z t, op1 (op2 x y) (op2 z t) = op2 (op1 x z) (op1 y t).

(* -------------------------------------------------------------------- *)
op pswap ['a 'b] (x : 'a * 'b) = (x.`2, x.`1).

lemma pswapK ['a 'b] : cancel pswap<:'a, 'b> pswap.
proof. by case. qed.

lemma bij_pswap ['a 'b] : bijective pswap<:'a, 'b>.
proof. by exists pswap; rewrite !pswapK. qed.

(* -------------------------------------------------------------------- *)
op pred0  ['a] = fun (x : 'a) => false.
op predT  ['a] = fun (x : 'a) => true.
op predI  ['a] = fun (p1 p2 : 'a -> bool) x => p1 x /\ p2 x.
op predU  ['a] = fun (p1 p2 : 'a -> bool) x => p1 x \/ p2 x.
op predC  ['a] = fun (p : 'a -> bool) x => ! (p x).
op predD  ['a] = fun (p1 p2 : 'a -> bool) x => !p2 x /\ p1 x.

op pred1  ['a] = fun (c x : 'a) => x = c.
op predU1 ['a] = fun (c : 'a) (p : 'a -> bool) (x : 'a) => x = c \/ p x.
op predC1 ['a] = fun (c : 'a) (x : 'a) => x <> c.
op predD1 ['a] = fun (p : 'a -> bool) (c : 'a) (x : 'a) => x <> c /\ p x.

(* -------------------------------------------------------------------- *)
type 'a rel = 'a -> 'a -> bool.

op rel0  ['a 'b] = fun (x : 'a) (y : 'b) => false.
op relT  ['a 'b] = fun (x : 'a) (y : 'b) => true.
op relI  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => p1 a b /\ p2 a b.
op relU  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => p1 a b \/ p2 a b.
op relC  ['a 'b] = fun (p : 'a -> 'b -> bool) a b => ! (p a b).
op relD  ['a 'b] = fun (p1 p2 : 'a -> 'b -> bool) a b => !p2 a b /\ p1 a b.

op rel1  ['a 'b] = fun (ca : 'a) (cb : 'b) a b => ca = a /\ cb = b.

op relU1 ['a 'b] =
  fun (ca : 'a) (cb : 'b) (p : 'a -> 'b -> bool) (a : 'a) (b : 'b) =>
    (a = ca /\ b = cb) \/ p a b.

op relC1 ['a 'b] =
  fun (ca : 'a) (cb : 'b) (a : 'a) (b : 'b) =>
    a <> ca /\ b <> cb.

op relD1 ['a 'b] =
  fun (p : 'a -> 'b -> bool) (ca : 'a) (cb : 'b) (a : 'a) (b : 'b) =>
    (a <> ca \/ b <> cb) /\ p a b.

(* -------------------------------------------------------------------- *)
pred total ['a] (R : 'a -> 'a -> bool) = forall x y, R x y \/ R y x.

pred transitive ['a] (R : 'a -> 'a -> bool) =
  forall y x z, R x y => R y z => R x z.

(* -------------------------------------------------------------------- *)
pred symmetric ['a] (R : 'a -> 'a -> bool) = forall x y, R x y = R y x.

pred antisymmetric ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y /\ R y x => x = y.

pred pre_symmetric ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => R y x.

(* -------------------------------------------------------------------- *)
pred reflexive ['a] (R : 'a -> 'a -> bool) = forall x, R x x.

pred irreflexive ['a] (R : 'a -> 'a -> bool) = forall x, !R x x.

(* -------------------------------------------------------------------- *)
pred left_transitive ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => R x == R y.

pred right_transitive ['a] (R : 'a -> 'a -> bool) =
  forall x y, R x y => transpose R x == transpose R y.

(* -------------------------------------------------------------------- *)
lemma nosmt congr1 ['a 'b] (f : 'a -> 'b) x1 x2 :
  x1 = x2 => f x1 = f x2
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andaE a b : (a && b) <=> (a /\ b) by [].
lemma nosmt oraE  a b : (a || b) <=> (a \/ b) by [].

(* -------------------------------------------------------------------- *)
lemma eqboolP (b1 b2 : bool) : (b1 = b2) <=> (b1 <=> b2) by [].

(* -------------------------------------------------------------------- *)
(* These should be declared as externals (SMT-LIB knows them)
   external (\x): bool -> bool -> bool.
   external ite : bool -> bool -> bool -> bool. *)

(* op (&&) b1 b2 = if b1 then b2 else false. *)
(* op (||) b1 b2 = if b1 then true else b2. *)
op (^) b1 b2  = if b1 then !b2 else b2.

(* -------------------------------------------------------------------- *)
lemma nosmt negP: forall (x:bool), (x => false) <=> !x by [].

lemma nosmt eqT : forall (x:bool), (x = true) <=> x by [].
lemma nosmt neqF : forall (x:bool), (x = false) <=> !x by [].

lemma nosmt negbT b  : b = false => !b by [].
lemma nosmt negbTE b : !b => b = false by [].
lemma nosmt negbF b  : b => !b = false by [].
lemma nosmt negbFE b : !b = false => b by [].
lemma nosmt negbK    : involutive [!]  by [].
lemma nosmt negbNE b : !!b => b        by [].

lemma nosmt negb_inj : injective [!]      by [].
lemma nosmt negbLR b c : b = !c => !b = c by [].
lemma nosmt negbRL b c : !b = c => b = !c by [].

lemma nosmt contra   c b : (c => b) => !b => !c by [].
lemma nosmt contraL  c b : (c => !b) => b => !c by [].
lemma nosmt contraR  c b : (!c => b) => !b => c by [].
lemma nosmt contraLR c b : (!c => !b) => b => c by [].
lemma nosmt contraT  b   : (!b => false) => b   by [].

lemma nosmt absurd (b a : bool) : (!a => !b) => b => a by [].

lemma nosmt wlog_neg b : (!b => b) => b by [].

lemma nosmt contraFT c b : (!c => b) => b = false => c by [].
lemma nosmt contraFN c b : (c => b) => b = false => !c by [].
lemma nosmt contraTF c b : (c => !b) => b => c = false by [].
lemma nosmt contraNF c b : (c => b) => !b => c = false by [].
lemma nosmt contraFF c b : (c => b) => b = false => c = false by [].

lemma nosmt contraNneq (b : bool) (x y : 'a):
  (x = y => b) => !b => x <> y
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt iffLR (a b : bool) : (a <=> b) => a => b by [].
lemma nosmt iffRL (a b : bool) : (a <=> b) => b => a by [].

lemma iff_negb : forall b1 b2, (!b1 <=> !b2) <=> (b1 <=> b2) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt if_congr ['a] (e e' : bool) (c1 c2 c1' c2': 'a) :
     e = e' => c1 = c1' => c2 = c2'
  => (if e then c1 else c2) = (if e' then c1' else c2')
by [].

lemma nosmt if_same b (vT : 'a) :
  (if b then vT else vT) = vT
by [].

lemma  if_neg b (vT vF : 'a) :
  (if !b then vT else vF) = if b then vF else vT
by [].

lemma  fun_if ['a 'b] (f:'a -> 'b) b x1 x2 :
  f (if b then x1 else x2) = (if b then f x1 else f x2)
by [].

lemma  fun_if2 ['a 'b 'c] (f:'a -> 'b -> 'c) b x1 x2 x :
  f (if b then x1 else x2) x = (if b then f x1 x else f x2 x)
by [].

lemma  if_arg b x (fT fF : 'a -> 'b) :
  (if b then fT else fF) x = if b then fT x else fF x
by [].

lemma  iffP p q r :
  (r <=> q) => (p => q) => (q => p) => r <=> p
by [].

lemma iffE (b1 b2 : bool) :
  (b1 <=> b2) <=> ((b1 => b2) /\ (b2 => b1))
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andTb : left_id true (/\)       by [].
lemma nosmt andFb : left_zero false (/\)    by [].
lemma nosmt andbT : right_id true (/\)      by [].
lemma nosmt andbF : right_zero false (/\)   by [].
lemma nosmt andbb : idempotent (/\)         by [].
lemma nosmt andbC : commutative (/\)        by [].
lemma nosmt andbA : associative (/\)        by [].
lemma nosmt andbCA : left_commutative (/\)  by [].
lemma nosmt andbAC : right_commutative (/\) by [].
lemma nosmt andbACA : interchange (/\) (/\) by [].

lemma nosmt orTb : forall b, true \/ b     by [].
lemma nosmt orFb : left_id false (\/)      by [].
lemma nosmt orbT : forall b, b \/ true     by [].
lemma nosmt orbF : right_id false (\/)     by [].
lemma nosmt orbb : idempotent (\/)         by [].
lemma nosmt orbC : commutative (\/)        by [].
lemma nosmt orbA : associative (\/)        by [].
lemma nosmt orbCA : left_commutative (\/)  by [].
lemma nosmt orbAC : right_commutative (\/) by [].
lemma nosmt orbACA : interchange (\/) (\/) by [].

lemma nosmt andbN b : (b /\ !b) <=> false by [].
lemma nosmt andNb b : (!b /\ b) <=> false by [].
lemma nosmt orbN b  : (b \/ !b) <=> true  by [].
lemma nosmt orNb b  : (!b \/ b) <=> true  by [].

lemma nosmt andb_orl : left_distributive  (/\) (\/)  by [].
lemma nosmt andb_orr : right_distributive (/\) (\/) by [].
lemma nosmt orb_andl : left_distributive  (\/) (/\)  by [].
lemma nosmt orb_andr : right_distributive (\/) (/\) by [].

lemma nosmt andb_idl a b : (b => a) => a /\ b <=> b by [].
lemma nosmt andb_idr a b : (a => b) => a /\ b <=> a by [].

lemma nosmt andb_id2l a b c : (a => b = c) => a /\ b <=> a /\ c by [].
lemma nosmt andb_id2r a b c : (b => a = c) => a /\ b <=> c /\ b by [].

lemma nosmt orb_idl a b : (a => b) => a \/ b <=> b by [].
lemma nosmt orb_idr a b : (b => a) => a \/ b <=> a by [].

lemma nosmt orb_id2l a b c : (!a => b = c) => a \/ b <=> a \/ c by [].
lemma nosmt orb_id2r a b c : (!b => a = c) => a \/ b <=> c \/ b by [].

lemma nosmt negb_and a b : !(a /\ b) <=> !a \/ !b by [].
lemma nosmt negb_or  a b : !(a \/ b) <=> !a /\ !b by [].

(* -------------------------------------------------------------------- *)
lemma nosmt negb_exists (P : 'a -> bool) :
  !(exists a, P a) <=> forall a, !P a
by [].

lemma nosmt negb_forall (P : 'a -> bool) :
  !(forall a, P a) <=> exists a, !P a
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andbK a b : a /\ b \/ a <=> a  by [].
lemma nosmt andKb a b : a \/ b /\ a <=> a  by [].
lemma nosmt orbK a b : (a \/ b) /\ a <=> a by [].
lemma nosmt orKb a b : a /\ (b \/ a) <=> a by [].

(* -------------------------------------------------------------------- *)
lemma nosmt implybT b : b => true         by [].
lemma nosmt implybF b : (b => false) = !b by [].
lemma nosmt implyFb b : false => b        by [].
lemma nosmt implyTb b : (true => b) = b   by [].
lemma nosmt implybb b : b => b            by [].

lemma nosmt negb_imply a b : !(a => b) <=> a /\ !b by [].

lemma nosmt implybE  a b : (a => b) <=> !a \/ b by [].
lemma nosmt implyNb  a b : (!a => b) <=> a \/ b by [].
lemma nosmt implybN  a b : (a => !b) <=> (b => !a) by [].
lemma nosmt implybNN a b : (!a => !b) <=> (b => a) by [].

lemma nosmt implyb_idl a b : (!a => b) => (a => b) <=> b by [].
lemma nosmt implyb_idr a b : (b => !a) => (a => b) <=> !a by [].

lemma nosmt implyb_id2l (a b c : bool) :
  (a => b <=> c) => (a => b) <=> (a => c)
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt addFb : left_id false (^)               by [].
lemma nosmt addbF : right_id false (^)              by [].
lemma nosmt addbb : self_inverse false (^)          by [].
lemma nosmt addbC : commutative (^)                 by [].
lemma nosmt addbA : associative (^)                 by [].
lemma nosmt addbCA : left_commutative (^)           by [].
lemma nosmt addbAC : right_commutative (^)          by [].
lemma nosmt addbACA : interchange (^) (^)           by [].
lemma nosmt andb_addl : left_distributive (/\) (^)  by [].
lemma nosmt andb_addr : right_distributive (/\) (^) by [].
lemma nosmt addKb : left_loop idfun (^)             by [].
lemma nosmt addbK : right_loop idfun (^)            by [].
lemma nosmt addIb : left_injective (^)              by [].
lemma nosmt addbI : right_injective (^)             by [].

lemma nosmt addTb b : true ^ b <=> !b by [].
lemma nosmt addbT b : b ^ true <=> !b by [].

lemma nosmt addbN a b : a ^ !b <=> !(a ^ b) by [].
lemma nosmt addNb a b : !a ^ b <=> !(a ^ b) by [].

lemma nosmt addbP a b : (!a <=> b) <=> (a ^ b) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andaP b1 b2 : b1 => (b1 => b2) => b1 /\ b2 by [].
lemma nosmt oraP  b1 b2 : b1 \/ b2 <=> b1 \/ (!b1 => b2) by [].

lemma nosmt andabP b1 b2 : b1 && b2 <=> b1 /\ b2 by [].
lemma nosmt orabP  b1 b2 : b1 || b2 <=> b1 \/ b2 by [].

(* -------------------------------------------------------------------- *)
lemma nosmt forall_orl (P : bool) (Q : 'a -> bool) :
  (P \/ (forall (x : 'a), Q x)) <=> forall (x : 'a), (P \/ Q x).
proof. by case: P. qed.

lemma nosmt forall_orr (P : bool) (Q : 'a -> bool) :
  ((forall (x : 'a), Q x) \/ P) <=> forall (x : 'a), (Q x \/ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt forall_andl (P : bool) (Q : 'a -> bool) :
  (P /\ (forall (x : 'a), Q x)) <=> forall (x : 'a), (P /\ Q x).
proof. by case: P. qed.

lemma nosmt forall_andr (P : bool) (Q : 'a -> bool) :
  ((forall (x : 'a), Q x) /\ P) <=> forall (x : 'a), (Q x /\ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt forall_eq (P P' : 'a -> bool) :
  (forall x, P x = P' x) =>
  (forall (x : 'a), P x) <=> (forall (x : 'a), P' x).
proof. by move=> h; split=> hP x; rewrite (h, -h) &(hP). qed.

lemma nosmt forall_eq_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x = Q' x)) =>
  (forall (x : 'a), P x => Q x) <=> (forall (x : 'a), P x => Q' x).
proof.
by move=> eq_Q; apply/forall_eq=> x /=; case (P x)=> // /eq_Q.
qed.

lemma nosmt forall_iff (P P' : 'a -> bool) :
  (forall x, P x <=> P' x) =>
  (forall (x : 'a), P x) <=> (forall (x : 'a), P' x).
proof. by move=> eq_P; split=> h x; have /eq_P:= h x. qed.

lemma nosmt forall_iff_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x <=> Q' x)) =>
  (forall (x : 'a), P x => Q x) <=> (forall (x : 'a), P x => Q' x).
proof.
by move=> eq_Q; apply/forall_iff=> x /=; case (P x)=> // /eq_Q.
qed.

(* -------------------------------------------------------------------- *)
lemma nosmt exists_orl (P : bool) (Q : 'a -> bool) :
  (P \/ (exists (x : 'a), Q x)) <=> exists (x : 'a), (P \/ Q x).
proof. by case: P. qed.

lemma nosmt exists_orr (P : bool) (Q : 'a -> bool) :
  ((exists (x : 'a), Q x) \/ P) <=> exists (x : 'a), (Q x \/ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt exists_andl (P : bool) (Q : 'a -> bool) :
  (P /\ (exists (x : 'a), Q x)) <=> exists (x : 'a), (P /\ Q x).
proof. by case: P. qed.

lemma nosmt exists_andr (P : bool) (Q : 'a -> bool) :
  ((exists (x : 'a), Q x) /\ P) <=> exists (x : 'a), (Q x /\ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma nosmt exists_eq (P P' : 'a -> bool) :
  (forall x, P x = P' x) =>
  (exists (x : 'a), P x) <=> (exists (x : 'a), P' x).
proof. by move=> eq; split=> -[x Px]; exists x; rewrite (eq, -eq). qed.

lemma nosmt exists_eq_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x = Q' x)) =>
  (exists (x : 'a), P x /\ Q x) <=> (exists (x : 'a), P x /\ Q' x).
proof.
by move=> eq_Q; apply/exists_eq=> x /=; case (P x)=> // /eq_Q.
qed.

lemma nosmt exists_iff (P P' : 'a -> bool) :
  (forall x, P x <=> P' x) =>
  (exists (x : 'a), P x) <=> (exists (x : 'a), P' x).
proof. by move=> eq_P; split; move=> [a] /eq_P h; exists a. qed.

lemma nosmt exists_iff_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x <=> Q' x)) =>
  (exists (x : 'a), P x /\ Q x) <=> (exists (x : 'a), P x /\ Q' x).
proof.
by move=> eq_Q; apply/exists_iff=> x /=; case (P x)=> // /eq_Q.
qed.

(* -------------------------------------------------------------------- *)
lemma  eq_refl  : forall (x : 'a), x = x by [].
lemma  eq_sym   : forall (x y : 'a), x = y <=> y = x by [].
lemma  eq_trans : forall (x y z : 'a), x = y => y = z => x = z by [].
lemma  eq_iff   : forall a b, (a = b) <=> (a <=> b) by [].

lemma  eq_sym_imp : forall (x y : 'a), x = y => y = x by [].

(* -------------------------------------------------------------------- *)
op choiceb ['a] (P : 'a -> bool) (x0 : 'a) : 'a.

axiom choicebP ['a] (P : 'a -> bool) (x0 : 'a):
  (exists x, P x) => P (choiceb P x0).

axiom choiceb_dfl ['a] (P : 'a -> bool) (x0 : 'a):
  (forall x, !P x) => choiceb P x0 = x0.

axiom nosmt eq_choice ['a] (P Q : 'a -> bool) (x0 : 'a):
  (forall x, P x <=> Q x) => choiceb P x0 = choiceb Q x0.

axiom nosmt choice_dfl_irrelevant ['a] (P : 'a -> bool) (x0 x1 : 'a):
  (exists x, P x) => choiceb P x0 = choiceb P x1.

(* -------------------------------------------------------------------- *)
axiom nosmt funchoice ['a 'b] (P : 'a -> 'b -> bool):
     (forall x, exists y, P x y)
  => (exists f, forall x, P x (f x)).

(* -------------------------------------------------------------------- *)
op sempty ['a] (E : 'a -> bool) =
  forall x, !E x.

lemma semptyNP ['a] (E : 'a -> bool) :
  !sempty E <=> exists x, E x.
proof. by rewrite /sempty -negb_exists. qed.
