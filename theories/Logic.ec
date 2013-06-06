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

lemma eq_tuple2_elim :
 forall 
    (x1:'a1) (x2:'a2)
    (y1:'a1) (y2:'a2) c,
    (x1,x2) = (y1,y2) =>
    (x1 = y1 => x2 = y2 => c) => c.

lemma eq_tuple3_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3)
    (y1:'a1) (y2:'a2) (y3:'a3) c,
    (x1,x2,x3) = (y1,y2,y3) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => c) => c.

lemma eq_tuple4_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) c,
    (x1,x2,x3,x4) = (y1,y2,y3,y4) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => c) => c.

lemma eq_tuple5_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) c,
    (x1,x2,x3,x4,x5) = (y1,y2,y3,y4,y5) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => x5 = y5 => c) => c.

lemma eq_tuple6_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) c,
    (x1,x2,x3,x4,x5,x6) = (y1,y2,y3,y4,y5,y6) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => x5 = y5 => x6 = y6 => c) => c.

lemma eq_tuple7_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7) c,
    (x1,x2,x3,x4,x5,x6,x7) = (y1,y2,y3,y4,y5,y6,y7) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => x5 = y5 => x6 = y6 => x7 = y7 => c) => c.

lemma eq_tuple8_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7) (y8:'a8) c,
    (x1,x2,x3,x4,x5,x6,x7,x8) = (y1,y2,y3,y4,y5,y6,y7,y8) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => x5 = y5 => x6 = y6 => x7 = y7 =>
    x8 = y8 => c) => c.

lemma eq_tuple9_elim : 
  forall 
    (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8) (x9:'a9)
    (y1:'a1) (y2:'a2) (y3:'a3) (y4:'a4) (y5:'a5) (y6:'a6) (y7:'a7) (y8:'a8) (y9:'a9) c,
    (x1,x2,x3,x4,x5,x6,x7,x8,x9) = (y1,y2,y3,y4,y5,y6,y7,y8,y9) =>
    (x1 = y1 => x2 = y2 => x3 = y3 => x4 = y4 => x5 = y5 => x6 = y6 => x7 = y7 =>
    x8 = y8 => x9 = y9 => c) => c .

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






