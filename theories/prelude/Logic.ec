(* -------------------------------------------------------------------- *)
require import Tactics.

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
type 'a wrapped = [Wrap of 'a].
op unwrap (w : 'a wrapped) =
  with w = Wrap x => x.

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
op "_.[_<-_]" ['a, 'b] (f : 'a -> 'b) (x : 'a) (y : 'b) =
  fun x' => if x = x' then y else f x'.

lemma fupdateE ['a 'b] (f : 'a -> 'b) (x x' : 'a) (y : 'b) :
  f.[x <- y] x' = if x = x' then y else f x'.
proof. by []. qed.

lemma fupdate_eq ['a 'b] (f : 'a -> 'b) (x : 'a) (y : 'b) :
  f.[x <- y] x = y.
proof. by []. qed.

lemma fupdate_neq ['a 'b] (f : 'a -> 'b) (x x' : 'a) (y : 'b) :
  x <> x' => f.[x <- y] x' = f x'.
proof. by move=> @/"_.[_<-_]" ->. qed.

(* -------------------------------------------------------------------- *)
pred preim ['a 'b] (f : 'a -> 'b) p x = p (f x).

(* -------------------------------------------------------------------- *)
abbrev [-printing] transpose ['a 'b 'c] (f : 'a -> 'b -> 'c) (y : 'b) =
  fun x => f x y.

lemma transposeP ['a, 'b, 'c] (f : 'a -> 'b -> 'c) (x : 'a) (y : 'b) : f x y = transpose f y x by done.

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
op injective (f : 'a -> 'b) =
  forall x y, f x = f y => x = y.

op surjective (f: 'a -> 'b) =
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
lemma congr1 ['a 'b] (f : 'a -> 'b) x1 x2 :
  x1 = x2 => f x1 = f x2
by [].

(* -------------------------------------------------------------------- *)
lemma andaE a b : (a && b) <=> (a /\ b) by [].
lemma oraE  a b : (a || b) <=> (a \/ b) by smt().

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
lemma negP: forall (x:bool), (x => false) <=> !x by [].

lemma eqT : forall (x:bool), (x = true) <=> x by smt().
lemma neqF : forall (x:bool), (x = false) <=> !x by smt().

lemma negbT b  : b = false => !b by [].
lemma negbTE b : !b => b = false by smt().
lemma negbF b  : b => !b = false by smt().
lemma negbFE b : !b = false => b by smt().
lemma negbK    : involutive [!]  by [].
lemma negbNE b : !!b => b        by [].

lemma negb_inj : injective [!]      by smt().
lemma negbLR b c : b = !c => !b = c by smt().
lemma negbRL b c : !b = c => b = !c by smt().

lemma contra   c b : (c => b) => !b => !c by smt().
lemma contraL  c b : (c => !b) => b => !c by smt().
lemma contraR  c b : (!c => b) => !b => c by smt().
lemma contraLR c b : (!c => !b) => b => c by smt().
lemma contraT  b   : (!b => false) => b   by [].

lemma absurd (b a : bool) : (!a => !b) => b => a by smt().

lemma wlog_neg b : (!b => b) => b by smt().

lemma contraFT c b : (!c => b) => b = false => c by [].
lemma contraFN c b : (c => b) => b = false => !c by [].
lemma contraTF c b : (c => !b) => b => c = false by smt().
lemma contraNF c b : (c => b) => !b => c = false by smt().
lemma contraFF c b : (c => b) => b = false => c = false by smt().

lemma contraNneq (b : bool) (x y : 'a):
  (x = y => b) => !b => x <> y
by smt().

(* -------------------------------------------------------------------- *)
lemma iffLR (a b : bool) : (a <=> b) => a => b by [].
lemma iffRL (a b : bool) : (a <=> b) => b => a by [].

lemma iff_negb : forall b1 b2, (!b1 <=> !b2) <=> (b1 <=> b2) by [].

(* -------------------------------------------------------------------- *)
lemma if_congr ['a] (e e' : bool) (c1 c2 c1' c2': 'a) :
     e = e' => c1 = c1' => c2 = c2'
  => (if e then c1 else c2) = (if e' then c1' else c2')
by [].

lemma if_same b (vT : 'a) :
  (if b then vT else vT) = vT
by [].

(* -------------------------------------------------------------------- *)
lemma iftrue ['a] (b : bool) (x y : 'a) :
  b => (if b then x else y) = x.
proof. by move=> ->. qed.

lemma iffalse ['a] (b : bool) (x y : 'a) :
  !b => (if b then x else y) = y.
proof. by move=> ->. qed.

(* -------------------------------------------------------------------- *)
lemma  if_neg b (vT vF : 'a) :
  (if !b then vT else vF) = if b then vF else vT
by smt().

lemma  fun_if ['a 'b] (f:'a -> 'b) b x1 x2 :
  f (if b then x1 else x2) = (if b then f x1 else f x2)
by smt().

lemma  fun_if2 ['a 'b 'c] (f:'a -> 'b -> 'c) b x1 x2 x :
  f (if b then x1 else x2) x = (if b then f x1 x else f x2 x)
by smt().

lemma  if_arg b x (fT fF : 'a -> 'b) :
  (if b then fT else fF) x = if b then fT x else fF x
by smt().

lemma ifT (b : bool) (e1 e2 : 'a) : 
  b => (if b then e1 else e2) = e1 
by move=> ->.

lemma ifF (b : bool) (e1 e2 : 'a) : 
 !b => (if b then e1 else e2) = e2
by move=> ->.

lemma  iffP p q r :
  (r <=> q) => (p => q) => (q => p) => r <=> p
by [].

lemma iffE (b1 b2 : bool) :
  (b1 <=> b2) <=> ((b1 => b2) /\ (b2 => b1))
by [].

(* -------------------------------------------------------------------- *)
lemma andTb : left_id true (/\)       by [].
lemma andFb : left_zero false (/\)    by [].
lemma andbT : right_id true (/\)      by [].
lemma andbF : right_zero false (/\)   by [].
lemma andbb : idempotent (/\)         by smt().
lemma andbC : commutative (/\)        by move=> [] /#.
lemma andbA : associative (/\)        by move=> [] /#.
lemma andbCA : left_commutative (/\)  by move=> [] /#.
lemma andbAC : right_commutative (/\) by move=> [] /#.
lemma andbACA : interchange (/\) (/\) by move=> [] /#.

lemma orTb : forall b, true \/ b     by [].
lemma orFb : left_id false (\/)      by [].
lemma orbT : forall b, b \/ true     by [].
lemma orbF : right_id false (\/)     by [].
lemma orbb : idempotent (\/)         by smt().
lemma orbC : commutative (\/)        by smt().
lemma orbA : associative (\/)        by smt().
lemma orbCA : left_commutative (\/)  by smt().
lemma orbAC : right_commutative (\/) by smt().
lemma orbACA : interchange (\/) (\/) by smt().

lemma andbN b : (b /\ !b) <=> false by smt().
lemma andNb b : (!b /\ b) <=> false by smt().
lemma orbN b  : (b \/ !b) <=> true  by smt().
lemma orNb b  : (!b \/ b) <=> true  by smt().

lemma andb_orl : left_distributive  (/\) (\/) by move=> [] /#.
lemma andb_orr : right_distributive (/\) (\/) by move=> [] /#.
lemma orb_andl : left_distributive  (\/) (/\) by move=> [] /#.
lemma orb_andr : right_distributive (\/) (/\) by move=> [] /#.

lemma andb_idl a b : (b => a) => a /\ b <=> b by smt().
lemma andb_idr a b : (a => b) => a /\ b <=> a by smt().

lemma andb_id2l a b c : (a => b = c) => a /\ b <=> a /\ c by smt().
lemma andb_id2r a b c : (b => a = c) => a /\ b <=> c /\ b by smt().

lemma orb_idl a b : (a => b) => a \/ b <=> b by smt().
lemma orb_idr a b : (b => a) => a \/ b <=> a by smt().

lemma orb_id2l a b c : (!a => b = c) => a \/ b <=> a \/ c by smt().
lemma orb_id2r a b c : (!b => a = c) => a \/ b <=> c \/ b by smt().

lemma negb_and a b : !(a /\ b) <=> !a \/ !b by smt().
lemma negb_or  a b : !(a \/ b) <=> !a /\ !b by smt().

lemma andlP a b c : a => ((a /\ b) => c) => b => c by smt().
lemma andrP a b c : a => ((b /\ a) => c) => b => c by smt().

(* -------------------------------------------------------------------- *)
lemma negb_exists (P : 'a -> bool) :
  !(exists a, P a) <=> forall a, !P a
by smt().

lemma negb_forall (P : 'a -> bool) :
  !(forall a, P a) <=> exists a, !P a
by smt().

(* -------------------------------------------------------------------- *)
lemma andbK a b : a /\ b \/ a <=> a  by smt().
lemma andKb a b : a \/ b /\ a <=> a  by smt().
lemma orbK a b : (a \/ b) /\ a <=> a by smt().
lemma orKb a b : a /\ (b \/ a) <=> a by smt().

(* -------------------------------------------------------------------- *)
lemma implybT b : b => true         by [].
lemma implybF b : (b => false) = !b by [].
lemma implyFb b : false => b        by [].
lemma implyTb b : (true => b) = b   by [].
lemma implybb b : b => b            by [].

lemma negb_imply a b : !(a => b) <=> a /\ !b by smt().

lemma implybE  a b : (a => b) <=> !a \/ b by smt().
lemma implyNb  a b : (!a => b) <=> a \/ b by smt().
lemma implybN  a b : (a => !b) <=> (b => !a) by smt().
lemma implybNN a b : (!a => !b) <=> (b => a) by smt().

lemma implyb_idl a b : (!a => b) => (a => b) <=> b by smt().
lemma implyb_idr a b : (b => !a) => (a => b) <=> !a by smt().

lemma implyb_id2l (a b c : bool) :
  (a => b <=> c) => (a => b) <=> (a => c)
by smt().

(* -------------------------------------------------------------------- *)
lemma addFb : left_id false (^)               by [].
lemma addbF : right_id false (^)              by [].
lemma addbb : self_inverse false (^)          by smt().
lemma addbC : commutative (^)                 by smt().
lemma addbA : associative (^)                 by smt().
lemma addbCA : left_commutative (^)           by smt().
lemma addbAC : right_commutative (^)          by smt().
lemma addbACA : interchange (^) (^)           by smt().
lemma andb_addl : left_distributive (/\) (^)  by smt().
lemma andb_addr : right_distributive (/\) (^) by smt().
lemma addKb : left_loop idfun (^)             by smt().
lemma addbK : right_loop idfun (^)            by smt().
lemma addIb : left_injective (^)              by smt().
lemma addbI : right_injective (^)             by smt().

lemma addTb b : true ^ b <=> !b by [].
lemma addbT b : b ^ true <=> !b by [].

lemma addbN a b : a ^ !b <=> !(a ^ b) by smt().
lemma addNb a b : !a ^ b <=> !(a ^ b) by [].

lemma addbP a b : (!a <=> b) <=> (a ^ b) by smt().

(* -------------------------------------------------------------------- *)
lemma andaP b1 b2 : b1 => (b1 => b2) => b1 /\ b2 by smt().
lemma oraP  b1 b2 : b1 \/ b2 <=> b1 \/ (!b1 => b2) by smt().

lemma andabP b1 b2 : b1 && b2 <=> b1 /\ b2 by [].
lemma orabP  b1 b2 : b1 || b2 <=> b1 \/ b2 by smt().

(* -------------------------------------------------------------------- *)
(*FIXME: may be useless because of rewrite, or may not be.*)
lemma andb_id2 a b c d : (a <=> b) => (c <=> d) => ((a /\ c) <=> (b /\ d)) by [].
lemma or_andl a b : (a \/ b) <=> ((a /\ !b) \/ b) by smt().
lemma or_andr a b : (a \/ b) <=> (a \/ (!a /\ b)) by smt().
lemma and_impl a b : (a /\ b) <=> ((b => a) /\ b) by smt().
lemma and_impr a b : (a /\ b) <=> ( a /\ (a => b)) by smt().

lemma negb_eqbl a b : ! (a <=> b) <=> (!a <=> b) by smt().
lemma negb_eqbr a b : ! (a <=> b) <=> (a <=> !b) by smt().

(* -------------------------------------------------------------------- *)
lemma forall_orl (P : bool) (Q : 'a -> bool) :
  (P \/ (forall (x : 'a), Q x)) <=> forall (x : 'a), (P \/ Q x).
proof. by case: P. qed.

lemma forall_orr (P : bool) (Q : 'a -> bool) :
  ((forall (x : 'a), Q x) \/ P) <=> forall (x : 'a), (Q x \/ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma forall_andl (P : bool) (Q : 'a -> bool) :
  (P /\ (forall (x : 'a), Q x)) <=> forall (x : 'a), (P /\ Q x).
proof. by case: P. qed.

lemma forall_andr (P : bool) (Q : 'a -> bool) :
  ((forall (x : 'a), Q x) /\ P) <=> forall (x : 'a), (Q x /\ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma forall_eq (P P' : 'a -> bool) :
  (forall x, P x = P' x) =>
  (forall (x : 'a), P x) <=> (forall (x : 'a), P' x).
proof. by move=> h; split=> hP x; rewrite (h, -h) &(hP). qed.

lemma forall_eq_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x = Q' x)) =>
  (forall (x : 'a), P x => Q x) <=> (forall (x : 'a), P x => Q' x).
proof.
by move=> eq_Q; apply/forall_eq=> x /=; case (P x)=> // /eq_Q.
qed.

lemma forall_iff (P P' : 'a -> bool) :
  (forall x, P x <=> P' x) =>
  (forall (x : 'a), P x) <=> (forall (x : 'a), P' x).
proof. by move=> eq_P; split=> h x; have /eq_P:= h x. qed.

lemma forall_iff_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x <=> Q' x)) =>
  (forall (x : 'a), P x => Q x) <=> (forall (x : 'a), P x => Q' x).
proof.
by move=> eq_Q; apply/forall_iff=> x /=; case (P x)=> // /eq_Q.
qed.

(* -------------------------------------------------------------------- *)
lemma exists_orl (P : bool) (Q : 'a -> bool) :
  (P \/ (exists (x : 'a), Q x)) <=> exists (x : 'a), (P \/ Q x).
proof. by case: P. qed.

lemma exists_orr (P : bool) (Q : 'a -> bool) :
  ((exists (x : 'a), Q x) \/ P) <=> exists (x : 'a), (Q x \/ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma exists_andl (P : bool) (Q : 'a -> bool) :
  (P /\ (exists (x : 'a), Q x)) <=> exists (x : 'a), (P /\ Q x).
proof. by case: P. qed.

lemma exists_andr (P : bool) (Q : 'a -> bool) :
  ((exists (x : 'a), Q x) /\ P) <=> exists (x : 'a), (Q x /\ P).
proof. by case: P. qed.

(* -------------------------------------------------------------------- *)
lemma exists_eq (P P' : 'a -> bool) :
  (forall x, P x = P' x) =>
  (exists (x : 'a), P x) <=> (exists (x : 'a), P' x).
proof. by move=> eq; split=> -[x Px]; exists x; rewrite (eq, -eq). qed.

lemma exists_eq_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
  (forall x, P x => (Q x = Q' x)) =>
  (exists (x : 'a), P x /\ Q x) <=> (exists (x : 'a), P x /\ Q' x).
proof.
by move=> eq_Q; apply/exists_eq=> x /=; case (P x)=> // /eq_Q.
qed.

lemma exists_iff (P P' : 'a -> bool) :
  (forall x, P x <=> P' x) =>
  (exists (x : 'a), P x) <=> (exists (x : 'a), P' x).
proof. by move=> eq_P; split; move=> [a] /eq_P h; exists a. qed.

lemma exists_iff_in (P : 'a -> bool) (Q Q' : 'a -> bool) :
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

lemma eq_choice ['a] (P Q : 'a -> bool) (x0 : 'a):
  (forall x, P x <=> Q x) => choiceb P x0 = choiceb Q x0.
proof. smt(fun_ext). qed.

axiom choice_dfl_irrelevant ['a] (P : 'a -> bool) (x0 x1 : 'a):
  (exists x, P x) => choiceb P x0 = choiceb P x1.

(* -------------------------------------------------------------------- *)

(* (Canonical) partial inverse realised using [choiceb] *)
op pinv (f : 'a -> 'b) (y : 'b) : 'a option = 
  if exists x, y = f x then Some (choiceb (fun x, y = f x) witness) else None.

lemma pinvN (f:'a->'b) x: 
  (!exists y, x = f y) => pinv f x = None.
proof. smt(). qed.

lemma pinv_inv (f:'a->'b) x: 
  (exists y, x = f y) => omap f (pinv f x) = Some x.
proof. by move => [y fy] @/pinv; rewrite ifT; smt(choicebP). qed.

lemma pcancel_pinv (f : 'a->'b): 
  injective f => pcancel f (pinv f).
proof. by move => inj_f @/pcansel x; smt(pinv_inv). qed.


(* -------------------------------------------------------------------- *)
axiom funchoice ['a 'b] (P : 'a -> 'b -> bool):
     (forall x, exists y, P x y)
  => (exists f, forall x, P x (f x)).

(* -------------------------------------------------------------------- *)
op sempty ['a] (E : 'a -> bool) =
  forall x, !E x.

lemma semptyNP ['a] (E : 'a -> bool) :
  !sempty E <=> exists x, E x.
proof. by rewrite /sempty -negb_exists. qed.

(* Locking (use with `rewrite [...]lock /= unlock`) *)
op locked (x : 'a) = x axiomatized by unlock.
lemma lock (x : 'a) : x = locked x by rewrite unlock.
