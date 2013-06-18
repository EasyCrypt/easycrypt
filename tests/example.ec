require import Logic.
require import Int.


pred p : 'a.

(* admit *)
lemma l_admit : forall (x:'a), p x.
proof.
  admit.
save.

(* idtac *)
lemma l_idtac : true.
proof.
 idtac.
admit.
save.

(* intros *)
lemma l_intros : forall (x1 : 'a), p x1 => forall (x2 x3:'a), p x2 => p x3.
proof.
  intros x1 hx1 x2.
  intros x3 hx2.
  admit.
save.

lemma l_intros_let : forall (x1 : int), 
   let x2 = x1 + x1 in
   let x3 = x2 + x2 in 
   x3 = x3.
proof.
  intros x1 x2 x3. (* FIXME : printing of let hyp *)
  admit.
save.


(* generalize *)
lemma l_generalize : forall (x1 : 'a), p x1 => forall (x2 x3:'a), p x2 => p x3.
proof.
  intros x1 hx1 x2 x3 hx2.
  generalize x1 hx1.
  generalize hx2 x2.
  admit.
save. 


(* clear *)
lemma l_clear : forall (x1 : 'a), p x1 => forall (x2 x3:'a), p x2 => p x3.
proof.
  intros x1 hx1 x2 x3 hx2.

  generalize x1 hx1 x2 x3 hx2.
  clear hx1 x1. (* can be in any order x1 hx1 or hx1 x1 *)
  clear x2 x3 hx2.
  admit.
save. 

(* assumption *)
lemma l_assumption : forall a, a => a. 
proof.
  intros a h.
  assumption h.
save.

lemma l_assumption_no : forall a, a => a. 
proof.
 intros a h.
 assumption.
save.

lemma l_assumption_ax : forall (x:'a), p x.
proof.
 assumption l_admit <:'a>.
save.

(* smt *)
lemma l_smt : forall (x:'a), x = x.
proof.
  smt.
save.

(* Simplification
   beta                    beta reducition   (* beta redex *)
   iota                    iota reduction    (* case redex : let tuple, if *)
   zeta                    zeta reduction    (* let redex  : single let *)
   delta names             unfold names    
   delta                   unfold all names
   logic                   logical simplification 

   Reduction can be composed
   exemple : beta iota 

   The following short cuts are defined :

   simplify                beta iota zeta logic
   simplify names          beta iota zeta logic names
   simplify delta          beta iota zeta logic delta 
                           (* ie compute the normal form *)
   
 *)
lemma l_simplify_beta : forall (x:int), (lambda y , y = y) x
proof.
  beta.
  smt.
save.

lemma l_simplify_iota : forall (x y:int), 
   let (u,v) = (x, y) in
   let w = u in
   if true then (lambda z , z = z) w else false.
proof.
  iota.
  intros x y w.
  beta.
  delta w.
admit.
save.

op iff (x y : bool) : bool = x <=> y.
op and (x y : bool) : bool = x /\ y.
op or  (x y : bool) : bool = x \/ y.

lemma l_simplify_delta : iff (and true true) true.
proof.
  delta and.
  beta delta or.
  beta delta iff. 
  logic.
admit.
save.

lemma l_simplify_logic : iff (and true true) false /\ (true = true).
proof.
  logic.
  simplify and or iff.
admit.
save.

lemma l_normalize : iff (and true true) false /\ (true = true).
proof.
  simplify delta.
admit.
save.

(* change *)
lemma l_change : iff (and true true) false /\ (true = true).
proof.
  change false.
admit.
save.


(* UNITIZED UP TO HERE *)
(* split 
   try to apply one of the following lemmas proved in Logic :
 true_intro 
 and_intro 
 anda_intro
 iff_intro
 if_intro
 eq_refl
*)

lemma l_split_true : true.
proof.
  split.
save.

lemma l_eq : forall (x:int), x = x.
proof.
 intros x.
 split.
save.

lemma l_split_and : forall x y, x /\ y.
proof.
 intros x y.
 split.
 admit.  
 admit.
save.

lemma l_split_anda : forall x y, x && y.
proof.
 intros x y.
 split.
 admit.  
 admit.
save.

lemma l_split_iff : forall x y, x <=> y.
proof.
 intros x y.
 split.
 admit.  
 admit.
save.

lemma l_split_if : forall x y z, if x then y else z.
proof.
 intros x y z.
 split.
 admit.  
 admit.
save.

(* Remark : if the current goal do no start by a known constructor,
   the tactic try to perform head reduction to find a known constructor.
   Most of the tactics allow this
   Example :
*)

lemma l_split_and' : forall x y, let g = and x y in g.
proof.
 intros x y g.
 split.
 admit.
 admit.
save. 

pred pintro (x:int)  = forall y, x = y.
lemma l_intro_red : forall x, pintro x.
proof.
 intros x y.
admit.
save.

(* exists *)
lemma l_exists : exists (x y z: int), x = y.
proof.
 exists 0.
 exists 0, 1.
admit.
save.

(* left 
   try to apply one of the following lemmas proved in Logic :
   or_intro_l
   ora_intro_l
   Again application is performed upto head reduction.
*)
lemma l_left : forall x y, x \/ y.
proof.
 intros x y.
 left.
admit.
save. 

lemma l_lefta : forall x y, x || y.
proof.
 intros x y.
 left.
admit.
save.   

(* right 
   try to apply one of the following lemmas proved in Logic :
   or_intro_r
   ora_intro_r
   Again application is performed upto head reduction.
*)

lemma l_right : forall x y, x \/ y.
proof.
 intros x y.
 right.
admit.
save. 

lemma l_righta : forall x y, x || y.
proof.
 intros x y.
 right.
admit.
save.  

(* apply :
   apply (g<: > a b _)
   apply h (a,_,b)
   apply :(f) (a, _)
*)

(* lemma l_intros : forall (x1 : 'a), p x1 => forall (x2 x3:'a), p x2 => p x3 *)

lemma l_apply_lem : forall (x:'a), p x.
proof.
intros x.
apply (l_intros<:'a> x _ x x _).
admit.
admit.
save.

lemma l_apply_hyp : forall a b, (a => b) => a => b.
proof.
intros a b h1 h2.
apply (h1 _).
apply h2.
save.

lemma l_apply_form : forall a b, (a => a => b) => a => b.
proof.
 intros a b h1 h2.
 apply ((_:a => b) _).
 apply (h1 _).
 apply h2.
 apply h2.
save.

(* cut *)

lemma l_cut : forall a, a.
proof.
 intros a.
 cut h : false.
admit.
admit.
save.

(* elim : eliminate logical constructor 
   Try to apply on of the following lemma (defined in logic)
   false_elim 
   and_elim 
   anda_elim 
   or_elim 
   ora_elim 
   iff_elim 
   if_elim
*)
lemma l_elim_false : forall (p:bool), false => p /\ !p.
proof.
  intros p h.
  elim h.  (* eliminate a hypothesis *)
save.

lemma l_elim_and : true.
proof.
 elim (l_split_and true false).  (* eliminate the application of a lemma *)
 elim (l_split_and false true).
 intros _ _ h _; apply h.
save.

lemma l_elim_anda : true.
proof.
  elim (_:true && false). (* eliminate a formula *)
  admit.
  admit.
save.

lemma l_elim_or : true.
proof.
  elim (_:true \/ false).
  admit.
  admit.
  admit.
save.

lemma l_elim_ora : true.
proof.
  elim (_:true || false).
  admit.
  admit.
  admit.
save.

lemma l_elim_iff : true.
proof.
  elim (_:false <=> true).
  admit.
  admit.
save.

lemma l_elim_if :forall (a:bool), true.
proof.
 intros a.
 elim (_:if a then true else false).
 admit.
 admit.
 admit.
save.

(* case *)
lemma l_case : forall (a b:bool), if a then a /\ true else a /\ false.
proof.
 intros a b.
 case (a /\ b).
   admit.
 case a.
   admit.
   admit.
save.

(* rewrite *)
lemma l_rewrite : forall (x y:'a), (false => x = y) => x = y => y = x.
proof.
 intros x y h1 h2.
 rewrite h2.       (* hypothesis, or lemma *)
 rewrite <- (h1 _).  (* application of a hypothesis, or lemma *)
admit.
 rewrite (_:x = y).  (* forumula *)
admit.
 admit.
save.

lemma l_rewrite_eq : forall a, a => a.
proof.
intros a h.
rewrite (eqT a _).
apply h.
split.
save.

(* subst *)

lemma l_subst_x : forall (x y z : int),
   x = y + z => x + 1 = (y + z) + 1.
proof.
 intros x y z h.
 subst x.
 split.
save.

lemma l_subst_xz : forall (x y z : int),
   x = y + z => y = z => x + 1 = (z + z) + 1.
proof.
 intros x y z _ _.
 subst x z.
 split.
save.

lemma l_subst : forall (x y z : int),
   x = y + z => y = z => x + 1 = (z + z) + 1.
proof.
 intros x y z _ _.
 subst.
 split.
save.

(*
lemma l_subst_fail : forall (x y z : int),
   x = y + z => y = y => x + 1 = (z + z) + 1
proof.
 intros x y z _ _.
 subst y.
*)

(* elimT t l : 
   t : a term of type ty
   l : a lemma, or a hypothesis of the following forms :
       forall (p:ty -> bool) (x:ty), P1 => ... => Pn => p x
       forall (p:ty -> bool), P1 => ... => Pn => forall x, p x
it is usefull to apply induction lemma of case lemma
*)

type 'a mylist.
cnst nil : 'a mylist.
op cons : ('a, 'a mylist) -> 'a mylist.

axiom mylistcase : 
  forall (p: 'a mylist -> bool, l:'a mylist), 
    (l = nil => p nil) => 
    (forall x l', l = cons x l' => p (cons x l')) =>
    p l.

axiom mylist_ind : 
  forall (p: 'a mylist -> bool),
    (p nil) => 
    (forall x l', p l' => p (cons x l')) =>
    forall (l:'a mylist), p l.

lemma mylist_or : 
  forall (l : 'a mylist), 
    l = nil \/ exists x l', l = cons x l'.
proof.
 intros l; elimT mylistcase l.
 intros _;left;smt.
 intros x l' heq; right.   
 exists x, l'.
 smt.
save.

op length : 'a mylist -> int.

lemma length_non_neg: forall (xs:'a mylist), 0 <= length xs.
proof.
 intros xs.
 elimT mylist_ind xs.
admit.
admit.
save.

