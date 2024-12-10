(* ==================================================================== *)
(* Typeclass examples *)

(* -------------------------------------------------------------------- *)
require import AllCore List.

(* -------------------------------------------------------------------- *)
(* Set theory *)

type class ['a] artificial = {
  op myop : artificial * 'a
}.

op myopi ['a] : int * 'a = (0, witness<:'a>).

instance 'b artificial with ['b] int
  op myop = myopi<:'b>.

lemma reduce_tc : myop<:bool, int> = (0, witness).
proof.
class.
reflexivity.
qed.

(* -------------------------------------------------------------------- *)
type class witness = {
  op witness : witness
}.

print witness.

type class finite = {
  op enum     : finite list
  axiom enumP : forall (x : finite), x \in enum
}.

print enum.
print enumP.

type class countable = {
  op count : int -> countable
  axiom countP : forall (x : countable), exists (n : int), x = count n
}.

(* -------------------------------------------------------------------- *)
(* Simple algebraic structures *)

type class magma = {
  op mmul : magma -> magma -> magma
}.

print mmul.

type class semigroup <: magma = {
  axiom mmulA : associative mmul<:semigroup>
}.

print associative.

type class monoid <: semigroup = {
  op mid : monoid

  axiom mmulr0 : right_id mid mmul<:monoid>
  axiom mmul0r : left_id mid mmul<:monoid>
}.

type class group <: monoid = {
  op minv : group -> group

  axiom mmulN : left_inverse mid minv mmul
}.

type class ['a <: semigroup] semigroup_action = {
  op amul  : 'a -> semigroup_action -> semigroup_action

  axiom compatibility :
    forall (g h : 'a) (x : semigroup_action), amul (mmul g h) x = amul g (amul h x)
}.

type class ['a <: monoid] monoid_action <: 'a semigroup_action = {
  axiom identity : forall (x : monoid_action), amul mid<:'a> x = x
}.

(* TODO: why again is this not possible/a good idea? *)
(*type class finite_group <: group & finite = {}.*)

(* -------------------------------------------------------------------- *)
(* Advanced algebraic structures *)

type class comgroup = {
  op zero  : comgroup
  op ([-])   : comgroup -> comgroup
  op ( + )   : comgroup -> comgroup -> comgroup

  axiom addr0 : right_id zero ( + )
  axiom addrN : left_inverse zero ([-]) ( + )
  axiom addrC : commutative ( + )
  axiom addrA : associative ( + )
}.

type class comring <: comgroup = {
  op one   : comring
  op ( * ) : comring -> comring -> comring

  axiom mulr1  : right_id one ( * )
  axiom mulrC  : commutative ( * )
  axiom mulrA  : associative ( * )
  axiom mulrDl : left_distributive ( * ) ( + )
}.

type class ['a <: comring] commodule <: comgroup = {
  op ( ** )  : 'a -> commodule -> commodule

  axiom scalerDl : forall (a b : 'a) (x : commodule),
    (a + b) ** x = (a ** x) + (b ** x)
  axiom scalerDr : forall (a : 'a) (x y : commodule),
    a ** (x + y) = (a ** x) + (a ** y)
}.


(* ==================================================================== *)
(* Abstract type examples *)

(* TODO: finish the hierarchy here:
   https://en.wikipedia.org/wiki/Magma_(algebra) *)
type foo <: witness.
type fingroup <: group & finite.



(* TODO: printing typeclasses *)
print countable.
print magma.
print semigroup.
print monoid.
print group.
print semigroup_action.
print monoid_action.


(* ==================================================================== *)
(* Operator examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

op all_finite ['a <: finite] (p : 'a -> bool) =
  all p enum<:'a>.

op all_countable ['a <: countable] (p : 'a -> bool) =
  forall (n : int), p (count<:'a> n).

(* -------------------------------------------------------------------- *)
(* Simple algebraic structures *)

(* TODO: weird issue and/or inapropriate error message : bug in ecUnify select_op*)

print amul.
(*
op foo1 ['a <: semigroup, 'b <: 'a semigroup_action] = amul<:'a,'b>.
*)
op foo2 ['a <: semigroup, 'b <: 'a semigroup_action] (g : 'a) (x : 'b) = amul g x.
(*
op foo3 ['a <: semigroup, 'b <: 'a semigroup_action] (g : 'a) (x : 'b) = amul<:'a,'b> g x.
*)

op big ['a, 'b <: monoid] (P : 'a -> bool) (F : 'a -> 'b) (r : 'a list) =
  foldr mmul mid (map F (filter P r)).


(* ==================================================================== *)
(* Lemma examples *)

(* -------------------------------------------------------------------- *)
(* Set theory *)

lemma all_finiteP ['a <: finite] p : (all_finite p) <=> (forall (x : 'a), p x).
proof. by rewrite/all_finite allP; split=> Hp x; rewrite Hp enumP. qed.

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

(* TODO: we want to be able to give the list directly.*)
instance finite with bool
  op enum = bool_enum.

realize enumP.
proof. by case. qed.

(* -------------------------------------------------------------------- *)
(* Advanced algebraic structures *)

(*
op izero = 0.

instance comgroup with int
  op zero = izero
  op ( + )  = CoreInt.add
  op ([-])  = CoreInt.opp.

(* TODO: might be any of the two addr0, also apply fails but rewrite works.
   In ecScope, where instances are declared. *)
realize addr0 by rewrite addr0.
realize addrN by trivial.
realize addrC by rewrite addrC.
realize addrA by rewrite addrA.

op foo = 1 + 3.

print ( + ).
print foo.

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
  (*TODO: in the goal, the typeclass operator + should have been replaced with the + from CoreInt, but has not been.*)
  print mulrDl.
  move => x y z.
  class.
  apply Ring.IntID.mulrDl.
qed.

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
*)
