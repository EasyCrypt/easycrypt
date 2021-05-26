(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* -------------------------------------------------------------------- *)
lemma nosmt unitW (P : unit -> bool): P 
tt => forall x, P x by [].

(* -------------------------------------------------------------------- *)
lemma nosmt trueI : true by [].

lemma nosmt falseW (c : bool) : false => c by [].

lemma nosmt boolW (P : bool -> bool) :
  P true => P false => forall b, P b by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andW a b c : (a => b => c) => (a /\ b) => c by [].

lemma nosmt andWl a b : (a /\ b) => a by [].
lemma nosmt andWr a b : (a /\ b) => b by [].

lemma nosmt andI a b : a => b => (a /\ b) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt orW a b c : (a => c) => (b => c) => (a \/ b) => c by [].

lemma nosmt orIl a b : a => a \/ b by [].
lemma nosmt orIr a b : b => a \/ b by [].

(* -------------------------------------------------------------------- *)
lemma nosmt andaW a b c : (a => b => c) => (a && b) => c by [].

lemma nosmt andaWl a b : (a && b) => a by [].
lemma nosmt andaWr a b : (a && b) => (a => b) by [].

lemma nosmt andaI a b : a => (a => b) => (a && b) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt oraW a b c : (a => c) => (!a => b => c) => (a || b) => c by [].

lemma nosmt oraIl a b : a => a || b by [].
lemma nosmt oraIr a b : (!a => b) => a || b by [].

(* -------------------------------------------------------------------- *)
lemma nosmt iffW a b c : ((a => b) => (b => a) => c) => (a <=> b) => c by [].
lemma nosmt iffI a b : (a => b) => (b => a) => (a <=> b) by [].

lemma nosmt iffLR a b : (a <=> b) => a => b by [].
lemma nosmt iffRL a b : (a <=> b) => b => a by [].

(* -------------------------------------------------------------------- *)
lemma nosmt ifW a bt bf c :
  (a => bt => c) => (!a => bf => c) => (if a then bt else bf) => c
by [].

lemma nosmt ifI a bt bf :
  (a => bt) => (!a => bf) => if a then bt else bf
by [].

(* -------------------------------------------------------------------- *)
lemma nosmt orDandN : forall a b, ((b /\ a) \/ (!b /\ a)) = a by [].
lemma nosmt andDorN : forall a b, ((b /\ a) /\ (!b /\ a)) = false by [].

(* -------------------------------------------------------------------- *)
lemma nosmt cut_ a b : a => (a => b) => b by [].

lemma nosmt boolWE (p : bool -> bool) x :
   (x => p true) => (!x => p false) => p x
by [].

lemma nosmt dup p q : (p => p => q) => p => q by [].

lemma nosmt negeqF: forall (x:bool), !x => (x =  false) by [].
lemma nosmt negbTE: forall (x:bool), !x => (x => false) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt eq_refl  : forall (x : 'a), x = x by [].
lemma nosmt eq_sym   : forall (x y : 'a), x = y <=> y = x by [].
lemma nosmt eq_trans : forall (x y z : 'a), x = y => y = z => x = z by [].
lemma nosmt eq_iff   : forall a b, (a = b) <=> (a <=> b) by [].

lemma nosmt eq_sym_imp : forall (x y : 'a), x = y => y = x by [].
lemma nosmt eq_iff_imp : forall (x y : bool), (x <=> y) => (x = y) by [].

(* -------------------------------------------------------------------- *)
lemma nosmt congr1 ['b 'a] :
  forall (f : 'a -> 'b) (x1 x2 : 'a),
    x1 = x2 => f x1 = f x2
by [].

lemma nosmt if_congr ['a] (e e' : bool) (c1 c2 c1' c2': 'a) :
     e = e' => c1 = c1' => c2 = c2'
  => (if e then c1 else c2) = (if e' then c1' else c2')
by [].

lemma nosmt eq_ind ['a] x y (f:'a -> bool) : x = y => f x => f y by [].

(* -------------------------------------------------------------------- *)
lemma nosmt and3_s1 b1 b2 b3 : b1 => b2 && b3 => b1 && b2 && b3 by [].
lemma nosmt and3_s2 b1 b2 b3 : b2 => b1 && b3 => b1 && b2 && b3 by [].
lemma nosmt and3_s3 b1 b2 b3 : b3 => b1 && b2 => b1 && b2 && b3 by [].
