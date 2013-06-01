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

lemma eq_tuple2_intro :
  forall 
    (x1:'a1) (x2:'a2)
    (y1:'a1) (y2:'a2),
    x1 = y1 => 
    x2 = y2 => 
    (x1,x2) = (y1,y2).

lemma eq_tuple3_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3)
    (y1:'a1) (y2:'a2) (y3:'a3),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    (x1,x2,x3) = (y1,y2,y3).

lemma eq_tuple4_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    (x1,x2,x3,x4) = (y1,y2,y3,y4).

lemma eq_tuple5_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    x5 = y5 =>
    (x1,x2,x3,x4,x5) = (y1,y2,y3,y4,y5).

lemma eq_tuple6_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    x5 = y5 =>
    x6 = y6 =>
    (x1,x2,x3,x4,x5,x6) = (y1,y2,y3,y4,y5,y6).

lemma eq_tuple7_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    x5 = y5 =>
    x6 = y6 =>
    x7 = y7 =>
    (x1,x2,x3,x4,x5,x6,x7) = (y1,y2,y3,y4,y5,y6,y7).

lemma eq_tuple8_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7) (y8:'a8),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    x5 = y5 =>
    x6 = y6 =>
    x7 = y7 =>
    x8 = y8 =>
    (x1,x2,x3,x4,x5,x6,x7,x8) = (y1,y2,y3,y4,y5,y6,y7,y8).

lemma eq_tuple9_intro : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8) (x9:'a9)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7) (y8:'a8) (y9:'a9),
    x1 = y1 => 
    x2 = y2 => 
    x3 = y3 => 
    x4 = y4 =>
    x5 = y5 =>
    x6 = y6 =>
    x7 = y7 =>
    x8 = y8 =>
    x9 = y9 =>
    (x1,x2,x3,x4,x5,x6,x7,x8,x9) = (y1,y2,y3,y4,y5,y6,y7,y8,y9).



