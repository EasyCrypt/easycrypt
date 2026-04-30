(* -------------------------------------------------------------------- *)
lemma unitW (P : unit -> bool): P tt => forall x, P x by smt().

(* -------------------------------------------------------------------- *)
lemma trueI : true by smt().

lemma falseW (c : bool) : false => c by smt().

lemma boolW (P : bool -> bool) :
  P true => P false => forall b, P b by smt().

(* -------------------------------------------------------------------- *)
lemma andW a b c : (a => b => c) => (a /\ b) => c by smt().

lemma andWl a b : (a /\ b) => a by smt().
lemma andWr a b : (a /\ b) => b by smt().

lemma andI a b : a => b => (a /\ b) by smt().

(* -------------------------------------------------------------------- *)
lemma orW a b c : (a => c) => (b => c) => (a \/ b) => c by smt().

lemma orIl a b : a => a \/ b by smt().
lemma orIr a b : b => a \/ b by smt().

(* -------------------------------------------------------------------- *)
lemma andaW a b c : (a => b => c) => (a && b) => c by smt().

lemma andaWl a b : (a && b) => a by smt().
lemma andaWr a b : (a && b) => (a => b) by smt().
lemma andaWrs a b : (a && b) => b by smt().

lemma andaI a b : a => (a => b) => (a && b) by smt().
lemma andaIs a b : a => b => (a && b) by smt().

(* -------------------------------------------------------------------- *)
lemma oraW a b c : (a => c) => (!a => b => c) => (a || b) => c by smt().

lemma oraIl a b : a => a || b by smt().
lemma oraIr a b : (!a => b) => a || b by smt().

(* -------------------------------------------------------------------- *)
lemma iffW a b c : ((a => b) => (b => a) => c) => (a <=> b) => c by smt().
lemma iffI a b : (a => b) => (b => a) => (a <=> b) by smt().

lemma iffLR a b : (a <=> b) => a => b by smt().
lemma iffRL a b : (a <=> b) => b => a by smt().

(* -------------------------------------------------------------------- *)
lemma ifW a bt bf c :
  (a => bt => c) => (!a => bf => c) => (if a then bt else bf) => c
by smt().

lemma ifI a bt bf :
  (a => bt) => (!a => bf) => if a then bt else bf
by smt().

(* -------------------------------------------------------------------- *)
lemma orDandN : forall a b, ((b /\ a) \/ (!b /\ a)) = a by smt().
lemma andDorN : forall a b, ((b /\ a) /\ (!b /\ a)) = false by smt().

(* -------------------------------------------------------------------- *)
lemma cut_ a b : a => (a => b) => b by smt().

lemma boolWE (p : bool -> bool) x :
   (x => p true) => (!x => p false) => p x
by smt().

lemma dup p q : (p => p => q) => p => q by smt().

lemma negeqF: forall (x:bool), !x => (x =  false) by smt().
lemma negbTE: forall (x:bool), !x => (x => false) by smt().

(* -------------------------------------------------------------------- *)
lemma eq_refl  : forall (x : 'a), x = x by smt().
lemma eq_sym   : forall (x y : 'a), x = y <=> y = x by smt().
lemma eq_trans : forall (x y z : 'a), x = y => y = z => x = z by smt().
lemma eq_iff   : forall a b, (a = b) <=> (a <=> b) by smt().

lemma eq_sym_imp : forall (x y : 'a), x = y => y = x by smt().
lemma eq_iff_imp : forall (x y : bool), (x <=> y) => (x = y) by smt().

(* -------------------------------------------------------------------- *)
lemma congr1 ['b 'a] :
  forall (f : 'a -> 'b) (x1 x2 : 'a),
    x1 = x2 => f x1 = f x2
by smt().

lemma if_congr ['a] (e e' : bool) (c1 c2 c1' c2': 'a) :
     e = e' => c1 = c1' => c2 = c2'
  => (if e then c1 else c2) = (if e' then c1' else c2')
by smt().

lemma eq_ind ['a] x y (f:'a -> bool) : x = y => f x => f y by smt().

(* -------------------------------------------------------------------- *)
lemma and3_s1 b1 b2 b3 : b1 => b2 && b3 => b1 && b2 && b3 by smt().
lemma and3_s2 b1 b2 b3 : b2 => b1 && b3 => b1 && b2 && b3 by smt().
lemma and3_s3 b1 b2 b3 : b3 => b1 && b2 => b1 && b2 && b3 by smt().
