(* --------------------------------------------------------------------
 * Copyright IMDEA Software Institute / INRIA - 2013, 2014
 * -------------------------------------------------------------------- *)

(*** Base Logic Rules *)
(** cut *)
lemma nosmt cut_lemma : forall (a b: bool), a => (a => b) => b by [].

(** false *)
lemma nosmt falseE : forall (c : bool), false => c by [].

(** true *)
lemma nosmt trueI : true by [].

(** case *)
lemma nosmt bool_case_eq : forall (p:bool -> bool) (x:bool),
   (x => p true) =>
   (!x => p false) =>
   p x
by [].

lemma nosmt bool_case : forall (p:bool -> bool),
  (p true) =>
  (p false) =>
  (forall x, p x)
by [].

(** boolean rewriting *)
lemma nosmt eq_iff : forall (a b:bool), (a = b) <=> (a <=> b) by [].

lemma nosmt eqT : forall (x:bool), (x = true) <=> x by [].
lemma nosmt neqF : forall (x:bool), (x = false) <=> !x by [].

lemma nosmt not_def: forall (x:bool), (x => false) <=> !x by [].
lemma nosmt nnot: forall (x:bool), (!(!x)) = x by [].

lemma nosmt negbTE: forall (x:bool), !x => (x => false) by [].

lemma nosmt nand: forall (a b:bool), (!a) \/ (!b) <=> !(a /\ b) by [].
lemma nosmt nor : forall (a b:bool), (!a) /\ (!b) <=> !(a \/ b) by [].

lemma nosmt for_ex: forall (p:'a -> bool), !(exists (x:'a), !p x) => forall (x:'a), p x by [].
lemma nosmt ex_for: forall (p:'a -> bool), !(forall (x:'a), !p x) => exists (x:'a), p x by [].

lemma nosmt nexists: forall (p:'a -> bool), (forall (x:'a), !p x) => !exists (x:'a), p x by [].
lemma nosmt nforall: forall (p:'a -> bool), (exists (x:'a), !p x) => !forall (x:'a), p x by [].

(** absurd *)
lemma nosmt absurd  : forall (b a : bool), (!a => !b) => b => a by [].

lemma nosmt contra  (c b : bool) : (c  =>  b) => !b => !c by [].
lemma nosmt contraL (c b : bool) : ( c => !b) =>  b => !c by [].
lemma nosmt contraR (c b : bool) : (!c =>  b) => !b =>  c by [].

(** and *)
lemma nosmt andE : forall (a b c:bool), 
    (a => b => c) => (a /\ b) => c
by [].

lemma nosmt andEl : forall (a b:bool),
    (a /\ b) => a
by [].

lemma nosmt andEr : forall (a b:bool),
    (a /\ b) => b
by [].

lemma nosmt andI : forall (a b : bool), 
   a => b => (a /\ b)
by [].

lemma nosmt andA : forall (a b c : bool),
  ((a /\ b) /\ c) = (a /\ (b /\ c))
by [].

lemma nosmt andC : forall (a b : bool),
  (a /\ b) = (b /\ a)
by [].

lemma nosmt andK : forall (b : bool),
  (b /\ b) = b
by [].

lemma nosmt andT : forall (b : bool),
  (b /\ true) = b
by [].

lemma nosmt andF : forall (b : bool),
  (b /\ false) = false
by [].

(** or *)
lemma nosmt orE : forall (a b c:bool), 
    (a => c) => (b => c) => (a \/ b) => c
by [].

lemma nosmt orIl : forall (a b : bool),
  a => a \/ b
by [].

lemma nosmt orIr : forall (a b : bool),
  b => a \/ b
by [].

lemma nosmt orbA : forall (a b c : bool),
  (a \/ (b \/ c)) = ((a \/ b) \/ c)
by [].

lemma nosmt orbC : forall (a b : bool),
  (a \/ b) = (b \/ a)
by [].

lemma nosmt orbK : forall (b : bool),
  (b \/ b) = b
by [].

lemma nosmt orTb (b : bool): (true  \/ b) = true  by [].
lemma nosmt orFb (b : bool): (false \/ b) = b     by [].
lemma nosmt orbT (b : bool): (b \/ true ) = true  by [].
lemma nosmt orbF (b : bool): (b \/ false) = b     by [].

(** Distributivity and/or *)
lemma nosmt orDand : forall (a b c : bool),
  ((a \/ b) /\ c) = ((a /\ c) \/ (b /\ c))
by [].

lemma nosmt andDor : forall (a b c : bool),
  ((a /\ b) \/ c) = ((a \/ c) /\ (b \/ c))
by [].

(* variation usefull for phoare split tactic *)
lemma nosmt orDandN : forall a b, (b /\ a \/ !b /\ a) = a
by [].

lemma nosmt andDorN : forall a b, ((b /\ a) /\ (!b /\ a)) = false
by [].

(** anda *)
lemma nosmt andaE : forall (a b c:bool),
    (a => b => c) => (a && b) => c
by [].

lemma nosmt andaEl : forall (a b:bool),
  (a && b) => a
by [].

lemma nosmt andaEr : forall (a b:bool),
  (a && b) => (a => b)
by [].

lemma nosmt andaI : forall (a b : bool),
   a => (a => b) => (a && b)
by [].

lemma nosmt anda_and : forall (a b:bool),
  (a && b) <=> (a /\ b)
by [].

(** ora *)
lemma nosmt oraE : forall (a b c:bool),
    (a => c) => (!a => b => c) => (a || b) => c
by [].

lemma nosmt oraIl : forall (a b : bool),
  a => a || b
by [].

lemma nosmt oraIr : forall (a b : bool),
  (!a => b) => a || b
by [].

lemma nosmt ora_or : forall (a b:bool),
  (a || b) <=> (a \/ b)
by [].

(** iff *)
lemma nosmt iffE : forall (a b c:bool),
  ((a => b) => (b => a) => c) => (a <=> b) => c
by [].

lemma nosmt iffI : forall (a b : bool),
  (a => b) => (b => a) => (a <=> b)
by [].

lemma nosmt iffLR (a b : bool):
  (a <=> b) => a => b
by [].

lemma nosmt iffRL (a b : bool):
  (a <=> b) => b => a
by [].

(** if *)
lemma nosmt ifE : forall (a bt bf c: bool), 
  (a => bt => c) => (!a => bf => c)
    => (if a then bt else bf) => c
by [].

lemma nosmt ifI : forall (a bt bf : bool),
  (a => bt) => (!a => bf) => if a then bt else bf
by [].

lemma nosmt if_det a (bt bf:'a):
  bt = bf =>
  (if a then bt else bf) = bt
by [].

(** congruence and rewriting *)
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

lemma nosmt rewrite_bool (x : bool) (p:bool -> bool):
  x => p true => p x
by [].

lemma nosmt congr1 :
  forall (f : 'a -> 'b) (x1 x2 : 'a),
    x1 = x2 => f x1 = f x2
by [].

lemma nosmt fun_if: forall (f:'a -> 'b) b x1 x2,
  f (if b then x1 else x2) = (if b then f x1 else f x2)
by [].

lemma nosmt fun_if2: forall (f:'a -> 'b -> 'c) b x1 x2 x,
  f (if b then x1 else x2) x = (if b then f x1 x else f x2 x)
by [].

lemma nosmt imp   : forall (x y : bool), (x => y) <=> ((!x)\/y) by [].

(** equality *)
lemma nosmt eq_refl  : forall (x:'a), x = x by [].
lemma nosmt eq_sym   : forall (x y : 'a), x = y <=> y = x by [].
lemma nosmt eq_trans : forall (x y z : 'a), x = y => y = z => x = z by [].

(** tuples *) 
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
