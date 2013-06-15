lemma cut_lemma : forall (a b: bool), a => (a => b) => b by [].

lemma false_elim : forall (c : bool), false => c by [].

lemma and_elim : forall (a b c:bool), 
    (a /\ b) => (a => b => c) => c
by [].

lemma and_proj_l : forall (a b:bool),
    (a /\ b) => a
by [].

lemma and_proj_r : forall (a b:bool),
    (a /\ b) => b
by [].

lemma anda_elim : forall (a b c:bool),
    (a && b) => (a => b => c) => c
by [].

lemma or_elim : forall (a b c:bool), 
    (a \/ b) => (a => c) => (b => c) => c
by [].

lemma ora_elim : forall (a b c:bool),
    (a || b) => (a => c) => (!a => b => c) => c
by [].

lemma iff_elim : forall (a b c:bool),
  (a <=> b) => ((a => b) => (b => a) => c) => c
by [].

lemma if_elim : forall (a bt bf c: bool), 
  (if a then bt else bf) =>
  (a => bt => c) => (!a => bf => c) => c
by [].

lemma true_intro : true by [].

lemma and_intro : forall (a b : bool), 
   a => b => (a /\ b)
by [].

lemma anda_intro : forall (a b : bool),
   a => (a => b) => (a && b)
by [].

lemma or_intro_l : forall (a b : bool),
  a => a \/ b
by [].

lemma ora_intro_l : forall (a b : bool),
  a => a || b
by [].

lemma or_intro_r : forall (a b : bool),
  b => a \/ b
by [].

lemma ora_intro_r : forall (a b : bool),
  (!a => b) => a || b
by [].

lemma iff_intro : forall (a b : bool),
  (a => b) => (b => a) => (a <=> b)
by [].

lemma if_intro : forall (a bt bf : bool),
  (a => bt) => (!a => bf) => if a then bt else bf
by [].

lemma absurd : forall (a b : bool), (!a => !b) => b => a by [].
 
lemma rewrite_l : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x2 => p x1
by [].

lemma rewrite_r : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x1 => p x2
by [].

lemma rewrite_iff_l : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x2 => p x1
by [].

lemma rewrite_iff_r : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x1 => p x2
by [].

lemma case_eq_bool : forall (P:bool -> bool, x:bool),
   (x => P true) =>
   (!x => P false) =>
   P x
by [].

lemma eq_refl : forall (x:'a), x = x by [].
lemma eqT  : forall (x:bool), x => (x = true) by [].
lemma neqF : forall (x:bool), !x => (x = false) by [].

lemma eqT_iff : forall (x:bool), (x = true) <=> x by [].
lemma neqF_iff : forall (x:bool), (x = false) <=> !x by [].

lemma tuple2_ind : 
  forall 
    (p: ('a1*'a2) -> bool) 
    (t:'a1*'a2),
    (forall (x1:'a1) (x2:'a2), 
       t = (x1,x2) => p (x1,x2)) => 
    p t
by [].

lemma tuple3_ind : 
  forall 
    (p: ('a1*'a2*'a3) -> bool) 
    (t:'a1*'a2*'a3),
    (forall (x1:'a1) (x2:'a2) (x3:'a3), 
       t = (x1,x2,x3) => p (x1,x2,x3)) => 
    p t
by [].

lemma tuple4_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4) -> bool) 
    (t:'a1*'a2*'a3*'a4),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4), 
       t = (x1,x2,x3,x4) => p (x1,x2,x3,x4)) => 
    p t
by [].

lemma tuple5_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5), 
       t = (x1,x2,x3,x4,x5) => p (x1,x2,x3,x4,x5)) => 
    p t
by [].

lemma tuple6_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6), 
       t = (x1,x2,x3,x4,x5,x6) => p (x1,x2,x3,x4,x5,x6)) => 
    p t
by [].

lemma tuple7_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7), 
       t = (x1,x2,x3,x4,x5,x6,x7) => p (x1,x2,x3,x4,x5,x6,x7)) => 
    p t
by [].

lemma tuple8_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8) => p (x1,x2,x3,x4,x5,x6,x7,x8)) => 
    p t
by [].

lemma tuple9_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8) 
      (x9:'a9), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8,x9) => p (x1,x2,x3,x4,x5,x6,x7,x8,x9)) => 
    p t
by [].
