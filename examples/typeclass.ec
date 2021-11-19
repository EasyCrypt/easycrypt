(* =====================================================================*)
require import AllCore List.


(* ==================================================================== *)
(* Typeclass examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

type class finite = {
  op enum     : finite list
  axiom enumP : forall (x : finite), x \in enum
}.

type class countable = {
  op count : int -> countable
  axiom countP : forall (x : countable), exists (n : int), x = count n
}.

(* -------------------------------------------------------------------- *)
(* Simple algebraic structures *)

type class magma = {
  op mmul : magma -> magma -> magma
}.

(* TODO: when removing the type argument of associative, no explicit error message.
   Should work anyway and if not, have a readable error message.*)
type class semigroup <: magma = {
  axiom mmulA : associative<:semigroup> mmul
}.

(* TODO: why do I need this instead of using left_id and right_id directly?
   Or even specifying the type?
   Or even specifying semigroup and not magma? *)
pred left_id_mmul ['a <: semigroup] (e : 'a) = left_id e mmul.
pred right_id_mmul ['a <: semigroup] (e : 'a) = right_id e mmul.

type class monoid <: semigroup = {
  op mid : monoid

  axiom mmulr0 : left_id_mmul mid
  axiom mmul0r : right_id_mmul mid
}.

(* TODO: same. *)
pred left_inverse_mid_mmul ['a <: monoid] (inv : 'a -> 'a) = left_inverse mid inv mmul.

type class group <: monoid = {
  op minv : group -> group

  axiom mmulN : left_inverse_mid_mmul minv
}.

type class ['a <: group] action = {
  op amul  : 'a -> action -> action

  axiom identity :
    forall (x : action), amul mid x = x
  axiom compatibility :
    forall (g h : 'a) (x : action), amul (mmul g h) x = amul g (amul h x)
}.

(* TODO: make one of these work, and then finish the hierarchy here:
   https://en.wikipedia.org/wiki/Magma_(algebra) *)
(* type fingroup <: group & finite. *)
(* type fingroup <: group & finite = {}. *)
(* type class fingroup = group & finite. *)

(* TODO: we may want to rename mmul to ( + ) and build this from group *)
type class comgroup = {
  op zero  : comgroup
  op ([-]) : comgroup -> comgroup
  op ( + ) : comgroup -> comgroup -> comgroup

  axiom addr0 : left_id zero (+)
  axiom addrN : left_inverse zero ([-]) (+)
  axiom addrC : commutative (+)
  axiom addrA : associative (+)
}.

(* -------------------------------------------------------------------- *)
(* Advanced algebraic structures *)

(*TODO: we don't have here the issues we had with semigroup and monoid,
  probably because left_distributive was adequatly typed by ( * )
  before beign applied to ( + ). *)
type class comring <: comgroup = {
  op one   : comring
  op ( * ) : comring -> comring -> comring

  axiom mulr1  : left_id one ( * )
  axiom mulrC  : commutative ( * )
  axiom mulrA  : associative ( * )
  axiom mulrDl : left_distributive ( * ) ( + )
}.

type class ['a <: comring] commodule <: comgroup = {
  op ( ** )  : 'a -> commodule -> commodule

  axiom scalerDl : forall (a b : 'a) (x : commodule),
    (a + b) ** x = a ** x + b ** x
  axiom scalerDr : forall (a : 'a) (x y : commodule),
    a ** (x + y) = a ** x + a ** y
}.


(* ==================================================================== *)
(* Operator examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

op all_finite ['a <: finite] (p : 'a -> bool) =
  all p enum<:'a>.

op all_countable ['a <: countable] (p : 'a -> bool) =
  forall (n : int), p (count<:'a> n).


(* ==================================================================== *)
(* Lemma examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

(* TODO: why is the rewrite/all_finite needed? *)
lemma all_finiteP ['a <: finite] p : (all_finite p) <=> (forall (x : 'a), p x).
proof. by rewrite/all_finite allP; split => Hp x; rewrite Hp // enumP. qed.

lemma all_countableP ['a <: countable] p : (all_countable p) <=> (forall (x : 'a), p x).
proof.
  rewrite/all_countable; split => [Hp x|Hp n].
    by case (countP x) => n ->>; rewrite Hp.
  by rewrite Hp.
qed.

lemma all_finite_countable ['a <: finite & countable] (p : 'a -> bool) : (all_finite p) <=> (all_countable p).
proof. by rewrite all_finiteP all_countableP. qed.

(* ==================================================================== *)
(* Instance examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

op bool_enum = [true; false].

(* TODO: we want to be ale to give the list directly.*)
instance finite with bool
  op enum = bool_enum.

realize enumP.
proof. by case. qed.

(* -------------------------------------------------------------------- *)
(* Simple algebraic structures *)

op izero = 0.

instance comgroup with int
  op zero  = izero
  op (+)   = CoreInt.add
  op ([-]) = CoreInt.opp.

realize addr0 by trivial.
realize addrN by trivial.
(* TODO: what? *)
(*
realize addrC by apply addrC.
realize addrC by apply Ring.IntID.addrC.
*)
realize addrC by rewrite addrC.
realize addrA by rewrite addrA.

(* -------------------------------------------------------------------- *)
(* Advanced algebraic structures *)

op ione = 1.

(* TODO: this automatically fetches the only instance of comgroup we have defined for int.
   We should give the choice of which instance to use, by adding  as desired_name after the with.
   Also we should give the choice to define directly an instance of comring with int. *)
instance comring with int
  op one   = ione
  op ( * ) = CoreInt.mul.

realize mulr1 by trivial.
realize mulrC by rewrite mulrC.
realize mulrA by rewrite mulrA.
realize mulrDl.
proof.
  print mulrDl.
  move => x y z.
  move: (Ring.IntID.mulrDl x y z).
  move => HmulrDl.
  (* TODO: what? *)
  admit.
qed.

type 'a poly = 'a list.

op pzero ['a] : 'a poly = [].
op padd  ['a <: comgroup] p q =
  mkseq (fun n => (nth zero<:'a> p n) + (nth zero<:'a> q n)) (max (size p) (size q)).
op pinv  ['a <: comgroup] = map [-]<:'a>.
op pone  ['a <: comring] = [one <:'a>].
op pmul  ['a <: comring] : 'a poly -> 'a poly -> 'a poly.
op ipmul ['a <: comring] (x : 'a) = map (( * ) x).

(* TODO: we may not need to specify the <:'a>. *)
instance comgroup with ['a <: comring] 'a poly
  op zero  = pzero<:'a>
  op (+)   = padd<:'a>
  op ([-]) = pinv<:'a>.

realize addr0.
proof.
  (* TODO: error message. *)
  move => x (*y*).
  (* Top.Logic turned into top... *)
  (* TODO: error message. *)
  (*rewrite //.*)
  (* TODO: wow I just broke something. *)
  (* rewrite /padd /pzero. *)
  admit.
qed.

realize addrN.
proof.
  (* TODO: all truly is broken. *)
  (*rewrite /pzero /padd.*)
  admit.
qed.

realize addrC by admit.
realize addrA by admit.

instance comring with ['a <: comring] 'a poly
  op one   = pone<:'a>
  op ( * ) = pmul<:'a>.

realize mulr1 by admit.
realize mulrC by admit.
realize mulrA by admit.
realize mulrDl by admit.

instance 'a commodule with ['a <: comring] 'a poly
  op ( ** ) = ipmul<:'a>.

realize scalerDl by admit.
realize scalerDr by admit.






(* ==================================================================== *)
(* Misc *)

(* -------------------------------------------------------------------- *)
(* TODO: which instance is kept in memory after this? *)

op bool_enum_alt = [true; false].

instance finite with bool
  op enum = bool_enum_alt.

realize enumP.
proof. by case. qed.

type class find_out <: finite = {
  axiom rev_enum : rev<:find_out> enum = enum
}.

instance find_out with bool.

realize rev_enum.
proof.
  admit.
qed.

(* -------------------------------------------------------------------- *)
(* TODO: some old bug that maybe already is fixed? *)

type class foo = {}.

type class tc  = {
  op foo : tc -> bool

  axiom foo_lemma : forall x, foo x
}.

op foo_int (x : int) = true.

instance tc with int
  op foo = foo_int.

realize foo_lemma.
proof. done. qed.

type class ['a <: foo] tc2 <: tc = {
  op bar : tc2 -> bool

  axiom bar_lemma : forall x, foo x => !bar x
}.

op bar_int (x : int) = false.

instance foo with bool.
instance foo with bool.

instance bool tc2 with int
  op bar = bar_int.             (* BUG *)

realize bar_lemma.
proof. done. qed.

op foo_2 ['a <: foo, 'b <: 'a tc2] = 0.



(* ==================================================================== *)
(* Old TODO list: 1-3 are done, modulo bugs, 4 is to be done, 5 will be done later. *)

(*
 1. typage -> selection des operateurs / inference des instances de tc
 2. reduction
 3. unification (tactiques)
 4. clonage
 5. envoi au SMT

 1.
   Fop :
     -(old) path * ty list -> form
     -(new) path * (ty * (map tcname -> tcinstance)) list -> form

   op ['a <: monoid] (+) : 'a -> 'a -> 'a.

   (+)<:int + monoid -> intadd_monoid>
   (+)<:int + monoid -> intmul_monoid>

   1.1 module de construction des formules avec typage
   1.2 utiliser le module ci-dessous

     let module M = MkForm(struct let env = env' end) in 

   1.3 UnionFind avec contraintes de TC

   1.4 Overloading:
       3 + 4
         a. 3 Int.(+) 4
         b. 3 Monoid<:int>.(+) 4 (-> instance du dessus -> ignore)

   1.5 foo<: int[monoid -> intadd_monoid] >
       foo<: int[monoid -> intmul_monoid] >

 2. -> Monoid.(+)<:int> -> Int.(+)

 3. -> Pb d'unification des op
         (+)<: ?[monoid -> ?] > ~ Int.(+)

       Mecanisme de resolution des TC

 4. -> il faut cloner les TC

 5.

   a. encodage

     record 'a premonoid = {
       op zero : 'a
       op add  : 'a -> 'a -> 'a;
     }

     pred ['a] ismonoid (m : 'a premonoid) = {
       left_id m.zero m.add
     }

     op ['a <: monoid] foo (x y : 'a) = x + y

     ->> foo ['a] (m : 'a premonoid) (x y : 'a) = m.add x y

     lemma foo ['a <: monoid] P

     ->> foo ['a] (m : 'a premonoid) : ismonoid m => P

     let intmonoid = { zero = 0; add = intadd }

     lemma intmonoid_is_monoid : ismonoid int_monoid

   b. reduction avant envoi
       (+)<: int[monoid -> intadd_monoid > -> Int.(+)

   c. ne pas envoyer certaines instances (e.g. int est un groupe)
      -> instance [nosmt] e.g.
*)
