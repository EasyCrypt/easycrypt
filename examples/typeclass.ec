(* -------------------------------------------------------------------- *)
require import AllCore List.

type class finite = {
  op enum     : finite list
  axiom enumP : forall (x : finite), x \in enum
}.

type class foo <: finite = {
}.

type class monoid = {
  op mzero : monoid
  op madd  : monoid -> monoid -> monoid
}.

(* instance monoid with int ... *)

type class group = {
  op zero  : group
  op ([-]) : group -> group
  op ( + ) : group -> group -> group

  axiom addr0 : left_id zero (+)
  axiom addrN : left_inverse zero ([-]) (+)
  axiom addrC : commutative (+)
  axiom addrA : associative (+)
}.

(* instance ['a <: group] monoid with 'a ... *)

type class ring <: group = {
  op one   : ring
  op ( * ) : ring -> ring -> ring

  axiom mulr1  : left_id one ( * )
  axiom mulrC  : commutative ( * )
  axiom mulrA  : associative ( * )
  axiom mulrDl : left_distributive ( * ) ( + )
}.

(* instance group with int ... *)

type class ['a <: ring] module_ <: group = {
  op ( ** )  : 'a -> module_ -> module_

  axiom scalerDl : forall (a b : 'a) (x : module_),
    (a + b) ** x = a ** x + b ** x

  axiom scalerDr : forall (a : 'a) (x y : module_),
    a ** (x + y) = a ** x + a ** y
}.

print ( ** ).

(*
type class A = ...
type class B1 <: A
type class B2 <: A
type class C <: B1 & B2

op ['a <: B1 & B2]

int -> group -> monoid
int -> monoid
*)

type 'a poly = 'a list.

op foo ['a <: group] (x y : 'a) = x + y.

lemma add0r ['a <: group] : right_id<:'a, 'a> zero (+).
proof.
  (* Works for bad reasons *)
  by move=> x /=; rewrite addrC addr0.
qed.

(* type fingroup <: group & finite. *)

(* type class fingroup = group & finite *)

(* -------------------------------------------------------------------- *)
op bool_enum = [true; false].

(* instance foo with bool. *)

instance finite with bool
  op enum = bool_enum.

realize enumP.
proof. by case. qed.


op all ['a <: finite] (p : 'a -> bool) =
  all p enum<:'a>.

(* -------------------------------------------------------------------- *)
op izero = 0.

instance group with int
  op zero  = izero
  op (+)   = CoreInt.add
  op ([-]) = CoreInt.opp.

(*TODO: what does Alt-Ergo have to do with this?*)
realize addr0 by [].
realize addrN by [].
realize addrC by [].
realize addrA by [].

op polyZ ['a <: ring] (c : 'a) (p : 'a poly) : 'a poly.

instance 'b module_ with ['b <: ring] 'b poly
  op ( ** ) = polyZ<:'b>.

instance ['a <: group & ...] 'a <: ... = {
}

instance ['a <: group] 'a <: monoid = {
}.

typeclass witness = {
  op witness : witness;
}.

instance ['a] 'a <: witness = {
}.

(* -------------------------------------------------------------------- *)

 1. typage -> selection des operateurs / inference des instances de tc
 2. reduction
 3. unification (tactiques)
 4. clonage
 5. envoi au SMT

 0. Define or find tcname

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
