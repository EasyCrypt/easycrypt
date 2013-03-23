lemma cut_lemma : forall (a b: bool), a => (a => b) => b.

lemma false_elim : forall (c : bool), false => c.

lemma and_elim : forall (a b c:bool), 
    (a /\ b) => (a => b => c) => c.

lemma anda_elim : forall (a b c:bool),
    (a && b) => (a => b => c) => c.

lemma or_elim : forall (a b c:bool), 
    (a \/ b) => (a => c) => (b => c) => c.

lemma ora_elim : forall (a b c:bool),
    (a || b) => (a => c) => (!a => b => c) => c.

lemma iff_elim : forall (a b c:bool),
  (a <=> b) => ((a => b) => (b => a) => c) => c.

lemma if_elim : forall (a bt bf c: bool), 
  (if a then bt else bf) =>
  (a => bt => c) => (!a => bf => c) => c.

lemma true_intro : true.

lemma and_intro : forall (a b : bool), 
   a => b => (a /\ b).

lemma anda_intro : forall (a b : bool),
   a => (a => b) => (a && b).

lemma or_intro_l : forall (a b : bool),
  a => a \/ b.

lemma ora_intro_l : forall (a b : bool),
  a => a || b.

lemma or_intro_r : forall (a b : bool),
  b => a \/ b.

lemma ora_intro_r : forall (a b : bool),
  (!a => b) => a || b.

lemma iff_intro : forall (a b : bool),
  (a => b) => (b => a) => (a <=> b).

lemma if_intro : forall (a bt bf : bool),
  (a => bt) => (!a => bf) => if a then bt else bf.


 
lemma rewrite_l : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x2 => p x1.

lemma rewrite_r : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x1 => p x2.

lemma rewrite_iff_l : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x2 => p x1.

lemma rewrite_iff_r : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x1 => p x2.

lemma case_eq_bool : forall (P:bool -> bool, x:bool),
   (x => P true) =>
   (!x => P false) =>
   P x.

lemma eq_refl : forall (x:'a), x = x.
lemma eqT  : forall (x:bool), x => (x = true).
lemma neqF : forall (x:bool), !x => (x = false).

lemma eqT_iff : forall (x:bool), (x = true) <=> x.
lemma neqF_iff : forall (x:bool), (x = false) <=> !x.







