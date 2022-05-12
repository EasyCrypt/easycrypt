(* -------------------------------------------------------------------- *)
lemma nosmt unitW (P : unit -> bool): P tt => forall x, P x by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt trueI : true by smt().

lemma nosmt falseW (c : bool) : false => c by smt().

lemma nosmt boolW (P : bool -> bool) :
  P true => P false => forall b, P b by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt andW a b c : (a => b => c) => (a /\ b) => c by smt().

lemma nosmt andWl a b : (a /\ b) => a by smt().
lemma nosmt andWr a b : (a /\ b) => b by smt().

lemma nosmt andI a b : a => b => (a /\ b) by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt orW a b c : (a => c) => (b => c) => (a \/ b) => c by smt().

lemma nosmt orIl a b : a => a \/ b by smt().
lemma nosmt orIr a b : b => a \/ b by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt andaW a b c : (a => b => c) => (a && b) => c by smt().

lemma nosmt andaWl a b : (a && b) => a by smt().
lemma nosmt andaWr a b : (a && b) => (a => b) by smt().

lemma nosmt andaI a b : a => (a => b) => (a && b) by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt oraW a b c : (a => c) => (!a => b => c) => (a || b) => c by smt().

lemma nosmt oraIl a b : a => a || b by smt().
lemma nosmt oraIr a b : (!a => b) => a || b by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt iffW a b c : ((a => b) => (b => a) => c) => (a <=> b) => c by smt().
lemma nosmt iffI a b : (a => b) => (b => a) => (a <=> b) by smt().

lemma nosmt iffLR a b : (a <=> b) => a => b by smt().
lemma nosmt iffRL a b : (a <=> b) => b => a by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt ifW a bt bf c :
  (a => bt => c) => (!a => bf => c) => (if a then bt else bf) => c
by smt().

lemma nosmt ifI a bt bf :
  (a => bt) => (!a => bf) => if a then bt else bf
by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt orDandN : forall a b, ((b /\ a) \/ (!b /\ a)) = a by smt().
lemma nosmt andDorN : forall a b, ((b /\ a) /\ (!b /\ a)) = false by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt cut_ a b : a => (a => b) => b by smt().

lemma nosmt boolWE (p : bool -> bool) x :
   (x => p true) => (!x => p false) => p x
by smt().

lemma nosmt dup p q : (p => p => q) => p => q by smt().

lemma nosmt negeqF: forall (x:bool), !x => (x =  false) by smt().
lemma nosmt negbTE: forall (x:bool), !x => (x => false) by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt eq_refl  : forall (x : 'a), x = x by smt().
lemma nosmt eq_sym   : forall (x y : 'a), x = y <=> y = x by smt().
lemma nosmt eq_trans : forall (x y z : 'a), x = y => y = z => x = z by smt().
lemma nosmt eq_iff   : forall a b, (a = b) <=> (a <=> b) by smt().

lemma nosmt eq_sym_imp : forall (x y : 'a), x = y => y = x by smt().
lemma nosmt eq_iff_imp : forall (x y : bool), (x <=> y) => (x = y) by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt congr1 ['b 'a] :
  forall (f : 'a -> 'b) (x1 x2 : 'a),
    x1 = x2 => f x1 = f x2
by smt().

lemma nosmt if_congr ['a] (e e' : bool) (c1 c2 c1' c2': 'a) :
     e = e' => c1 = c1' => c2 = c2'
  => (if e then c1 else c2) = (if e' then c1' else c2')
by smt().

lemma nosmt eq_ind ['a] x y (f:'a -> bool) : x = y => f x => f y by smt().

(* -------------------------------------------------------------------- *)
lemma nosmt and3_s1 b1 b2 b3 : b1 => b2 && b3 => b1 && b2 && b3 by smt().
lemma nosmt and3_s2 b1 b2 b3 : b2 => b1 && b3 => b1 && b2 && b3 by smt().
lemma nosmt and3_s3 b1 b2 b3 : b3 => b1 && b2 => b1 && b2 && b3 by smt().
