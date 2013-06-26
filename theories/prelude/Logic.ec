lemma nosmt cut_lemma : forall (a b: bool), a => (a => b) => b by [].

lemma nosmt false_elim : forall (c : bool), false => c by [].

lemma nosmt and_elim : forall (a b c:bool), 
    (a /\ b) => (a => b => c) => c
by [].

lemma nosmt and_proj_l : forall (a b:bool),
    (a /\ b) => a
by [].

lemma nosmt and_proj_r : forall (a b:bool),
    (a /\ b) => b
by [].

lemma nosmt anda_elim : forall (a b c:bool),
    (a && b) => (a => b => c) => c
by [].

lemma nosmt or_elim : forall (a b c:bool), 
    (a \/ b) => (a => c) => (b => c) => c
by [].

lemma nosmt ora_elim : forall (a b c:bool),
    (a || b) => (a => c) => (!a => b => c) => c
by [].

lemma nosmt iff_elim : forall (a b c:bool),
  (a <=> b) => ((a => b) => (b => a) => c) => c
by [].

lemma nosmt if_elim : forall (a bt bf c: bool), 
  (if a then bt else bf) =>
  (a => bt => c) => (!a => bf => c) => c
by [].

lemma nosmt true_intro : true by [].

lemma nosmt and_intro : forall (a b : bool), 
   a => b => (a /\ b)
by [].

lemma nosmt anda_intro : forall (a b : bool),
   a => (a => b) => (a && b)
by [].

lemma nosmt or_intro_l : forall (a b : bool),
  a => a \/ b
by [].

lemma nosmt ora_intro_l : forall (a b : bool),
  a => a || b
by [].

lemma nosmt or_intro_r : forall (a b : bool),
  b => a \/ b
by [].

lemma nosmt orA : forall (a b c : bool),
  ((a \/ b) \/ c) = (a \/ (b \/ c))
by [].

lemma nosmt andA : forall (a b c : bool),
  ((a /\ b) /\ c) = (a /\ (b /\ c))
by [].

lemma nosmt orDand : forall (a b c : bool),
  ((a \/ b) /\ c) = ((a /\ c) \/ (b /\ c))
by [].

lemma nosmt andDor : forall (a b c : bool),
  ((a /\ b) \/ c) = ((a \/ c) /\ (b \/ c))
by [].

lemma nosmt ora_intro_r : forall (a b : bool),
  (!a => b) => a || b
by [].

lemma nosmt iff_intro : forall (a b : bool),
  (a => b) => (b => a) => (a <=> b)
by [].

lemma nosmt if_intro : forall (a bt bf : bool),
  (a => bt) => (!a => bf) => if a then bt else bf
by [].

lemma nosmt absurd : forall (a b : bool), (!a => !b) => b => a by [].
 
lemma nosmt rewrite_l : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x2 => p x1
by [].

lemma nosmt rewrite_r : forall (x1 x2:'a) (p:'a -> bool),
  x1 = x2 => p x1 => p x2
by [].

lemma nosmt rewrite_iff_l : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x2 => p x1
by [].

lemma nosmt rewrite_iff_r : forall (x1 x2:bool) (p:bool -> bool),
  (x1 <=> x2) => p x1 => p x2
by [].

lemma nosmt case_eq_bool : forall (P:bool -> bool, x:bool),
   (x => P true) =>
   (!x => P false) =>
   P x
by [].

lemma nosmt eq_refl  : forall (x:'a), x = x by [].
lemma nosmt eq_sym   : forall (x y : 'a), x = y => y = x by [].
lemma nosmt eq_trans : forall (x y z : 'a), x = y => y = z => x = z by [].

lemma nosmt eqT  : forall (x:bool), x => (x = true) by [].
lemma nosmt neqF : forall (x:bool), !x => (x = false) by [].

lemma nosmt eqT_iff : forall (x:bool), (x = true) <=> x by [].
lemma nosmt neqF_iff : forall (x:bool), (x = false) <=> !x by [].

lemma nosmt fcongr :
  forall (f : 'a -> 'b) (x1 x2 : 'a),
    x1 = x2 => f x1 = f x2
by [].

lemma nosmt tuple2_ind : 
  forall 
    (p: ('a1*'a2) -> bool) 
    (t:'a1*'a2),
    (forall (x1:'a1) (x2:'a2), 
       t = (x1,x2) => p (x1,x2)) => 
    p t
by [].

lemma nosmt tuple3_ind : 
  forall 
    (p: ('a1*'a2*'a3) -> bool) 
    (t:'a1*'a2*'a3),
    (forall (x1:'a1) (x2:'a2) (x3:'a3), 
       t = (x1,x2,x3) => p (x1,x2,x3)) => 
    p t
by [].

lemma nosmt tuple4_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4) -> bool) 
    (t:'a1*'a2*'a3*'a4),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4), 
       t = (x1,x2,x3,x4) => p (x1,x2,x3,x4)) => 
    p t
by [].

lemma nosmt tuple5_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5), 
       t = (x1,x2,x3,x4,x5) => p (x1,x2,x3,x4,x5)) => 
    p t
by [].

lemma nosmt tuple6_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6), 
       t = (x1,x2,x3,x4,x5,x6) => p (x1,x2,x3,x4,x5,x6)) => 
    p t
by [].

lemma nosmt tuple7_ind : 
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7), 
       t = (x1,x2,x3,x4,x5,x6,x7) => p (x1,x2,x3,x4,x5,x6,x7)) => 
    p t
by [].

lemma nosmt tuple8_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8) => p (x1,x2,x3,x4,x5,x6,x7,x8)) => 
    p t
by [].

lemma nosmt tuple9_ind :
  forall 
    (p: ('a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9) -> bool) 
    (t:'a1*'a2*'a3*'a4*'a5*'a6*'a7*'a8*'a9),
    (forall (x1:'a1) (x2:'a2) (x3:'a3) (x4:'a4) (x5:'a5) (x6:'a6) (x7:'a7) (x8:'a8) 
      (x9:'a9), 
       t = (x1,x2,x3,x4,x5,x6,x7,x8,x9) => p (x1,x2,x3,x4,x5,x6,x7,x8,x9)) => 
    p t
by [].
