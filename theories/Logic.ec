lemma cut_lemma : forall (a b: bool), a => (a => b) => b.

lemma false_elim : forall (c : bool), false => c.

lemma and_elim : forall (a b c:bool), 
    (a /\ b) => (a => b => c) => c.

lemma and_proj_l : forall (a b:bool),
    (a /\ b) => a.

lemma and_proj_r : forall (a b:bool),
    (a /\ b) => b.

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

lemma tuple2_ind : 
  forall 
    (p: ('a1*'a2) -> bool) 
    (t:'a1*'a2),
    (forall (x1:'a1) (x2:'a2), 
       t = (x1,x2) => p (x1,x2)) => 
    p t.

lemma tuple3_ind : 
  forall 
    (p: ('a1*'a2*'a3) -> bool) 
    (t:'a1*'a2*'a3),
    (forall (x1:'a1) (x2:'a2) (x3:'a3), 
       t = (x1,x2,x3) => p (x1,x2,x3)) => 
    p t.

lemma tuple4_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4) -> bool) 
    (t:'a1*'a2*'a3*'a4),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4), 
       t = (x1,x2,x3,x4) => p (x1,x2,x3,x4)) => 
    p t.

lemma tuple5_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5), 
       t = (x1,x2,x3,x4,x5) => p (x1,x2,x3,x4,x5)) => 
    p t.

lemma tuple6_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6), 
       t = (x1,x2,x3,x4,x5,x6) => p (x1,x2,x3,x4,x5,x6)) => 
    p t.

lemma tuple7_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7), 
       t = (x1,x2,x3,x4,x5,x6,x7) => p (x1,x2,x3,x4,x5,x6,x7)) => 
    p t.

lemma tuple8_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8) => p (x1,x2,x3,x4,x5,x6,x7,x8)) => 
    p t.

lemma tuple9_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8) 
      (x9:'a9), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8,x9) => p (x1,x2,x3,x4,x5,x6,x7,x8,x9)) => 
    p t.






