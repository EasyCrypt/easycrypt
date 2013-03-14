require import Int.
require import Fun.

type 'a t.

cnst empty : 'a t.

op add    : ('a, 'a t) -> 'a t.

op singleton (x:'a) : 'a t = add x empty.

op pick   : 'a t -> 'a.
op rm     : ('a, 'a t) -> 'a t.
op union  : ('a t, 'a t) -> 'a t.
op inter  : ('a t, 'a t) -> 'a t.

op is_empty : 'a t -> bool.
axiom is_empty_empty : forall (X : 'a t), is_empty X <=> X = empty.


op mem      : ('a, 'a t) -> bool.
op Pmem (X:'a t, x:'a) : bool = mem x X.

axiom Set_ind : forall (P : ('a t) Pred),
P empty =>
(forall (S : 'a t, x : 'a), !mem x S => P S => P (add x S)) =>
 forall (S : 'a t), P S.

op card     : 'a t -> int.
axiom card1 : card<:'a> empty = 0.
axiom cadr2 : forall (S : 'a t, x : 'a), mem x S => card(S) = 1 + card(rm x S).

pred [==] (X1:'a t, X2:'a t) = 
 forall (x:'a), mem x X1 <=> mem x X2.

pred ext_eq (X1:'a t, X2:'a t) = X1 == X2. 

 (* extentional equality is an equivalence relation*)
lemma eq_refl :
 forall (X:'a t), X == X.

lemma eq_sym :
 forall (X Y:'a t), X == Y => Y == X.


lemma eq_trans :
 forall (X Y Z:'a t), X == Y => Y == Z => X == Z.


pred [<=] (X1:'a t, X2:'a t) = 
 forall (x:'a), mem x X1 => mem x X2.

 (* subset defines a Poset *)
lemma sub_refl :
 forall (X:'a t), X <= X.

lemma sub_anti_sym : 
 forall (X Y:'a t), X <= Y => Y <= X => X == Y.

lemma sub_trans :
 forall (X Y Z:'a t), X <= Y => Y <= Z => X <= Z.

axiom extentionality : 
 forall (X1:'a t, X2:'a t),
X1 = X2 <=> X1 == X2.


 (* Specification of is_empty *)
axiom is_empty_mem : forall (X:'a t), 
 is_empty X <=> forall (x:'a), !mem x X.

 (* local *) pred P_is_empty_card (X : 'a t) =
card X = 0 => is_empty X.

 (* Specification of empty *)

lemma empty_subset : forall(X:'a t),
 empty <= X.

 (* FIXME lemma *)
lemma empty_mem  : forall (x:'a), !mem x empty.

axiom empty_card : card<:'a>(empty) = 0.

 (* Specification of add *)

axiom add_mem : forall (x:'a, y:'a, X:'a t), 
 mem x (add y X) <=> mem x X || x = y.


axiom add_card : forall (x:'a, X:'a t), 
 !mem x X => card (add x X) = card X + 1.

lemma mem_add_aux : forall (x:'a, X:'a t),
mem x X => X == add x X.

lemma mem_add : forall (x:'a, X:'a t),
mem x X => X = add x X.

lemma add_subset : forall  (x:'a, X:'a t),
 X <= add x X.

lemma singleton_card : forall (x:'a),
card (singleton x) = 1.

 (* local *) pred P_card_pos (X : 'a t) = 0 <= card X.
lemma card_pos : forall (X:'a t), 0 <= card X
proof.
 intros X.
 cut H : (P_card_pos X).
 apply Set_ind<:'a>(P_card_pos,_,_,X);trivial.
 trivial.
save.


  (* filter *)
op filter : ('a Pred, 'a t) -> 'a t.

axiom filter_mem : forall (P:'a Pred, X:'a t, x:'a),
 mem x (filter P X) <=> (mem x X && P x).

axiom filter_card : forall (P:'a Pred, X : 'a t), 
card (filter P X) = card X - card(filter (Pnot P) X). 

axiom filter_Peq_in : forall (x:'a, X:'a t),
mem x X =>
filter (Peq x) X = singleton x.

axiom filter_Peq_card_in : forall (x:'a, X:'a t),
mem x X =>
card (filter (Peq x) X) = 1.

lemma filter_subset : forall (P:'a Pred, X:'a t),
 filter P X <= X.

 (* facts about pick *)
axiom pick_spec : forall (X : 'a t), 
 X <> empty => mem (pick X) X.

lemma pick_singleton : forall (x : 'a), 
pick (singleton x) = x.

 (* facts about rm *)
axiom rm_spec_not_mem : forall(X :'a t, x: 'a),
 !mem x X => rm x X = X.

axiom rm_spec_mem : forall(X :'a t, x: 'a),
mem x X => add x (rm x X) = X.

axiom rm_mem : forall (X : 'a t, x : 'a),
 !mem x (rm x X).

lemma rm_subs :  forall (X : 'a t, x : 'a),
 rm x X <= X.

lemma rm_card :  forall (X : 'a t, x : 'a),
 card(rm x X) <= card X.

lemma card_non_empty : forall (X : 'a t),
 forall (x :'a),
mem x X => card<:'a> X = 1 + card (rm x X).

lemma is_empty_card : forall (X:'a t),
card X = 0 => is_empty X 
proof.
 intros X.
 cut H : (P_is_empty_card X).
 apply Set_ind<:'a>(P_is_empty_card,_,_,X);trivial.
 trivial.
save.

  (* union *) 
axiom union_mem : forall(X:'a t, Y:'a t, x: 'a),
 mem x (union X Y) <=> (mem x X || mem x Y).

lemma union_empty : forall(X :'a t),
union X empty = X
proof.
 intros X.
 cut H : (union X empty == X).
 trivial.
 trivial.
save.

lemma union_empty_aux : forall(X :'a t),
union X empty == X.


lemma union_comm1 : forall(X:'a t, Y:'a t),
union X Y == union Y X.

lemma union_comm : forall(X:'a t, Y:'a t),
union X Y = union Y X.

lemma union_add_aux : forall(X:'a t, Y:'a t, x: 'a),
add x (union X Y) == union (add x X) Y.

lemma union_add : forall(X:'a t, Y:'a t, x: 'a),
add x (union X Y) = union (add x X) Y.

lemma subset_union1 : forall (X Y : 'a t),
 X <= union X Y.

 (* local *) pred P_subset_union (X : 'a t) = forall(Y : 'a t),
 X <= Y => exists (Z : 'a t), Y = union X Z.

lemma subset_union2 : forall (X : 'a t, Y : 'a t),
 X <= Y => exists (Z : 'a t), Y = union X Z
proof.
 intros X.
 cut H0 : (P_subset_union X).
 apply Set_ind<:'a>(P_subset_union,_,_,X).
 trivial.
 intros S x H H0.
 cut H1 : (forall (Y : 'a t), (add x S)<= Y => (exists (Z : 'a t), Y = union (add x S) Z)).
 intros Y H1.
 cut H2 : (S <= Y).
 trivial.
 cut H3 : (forall(Y : 'a t),
 S <= Y => exists (Z : 'a t), Y = union S Z).
 trivial.
 cut H4 : (exists (Z : 'a t), Y = union S Z).
 apply H3(Y,_).
 assumption.
 elim H4.
 intros Z H5.
 trivial.
 trivial.
 trivial.
save.


  (* local *) pred P_union_card1( X : 'a t) = forall(Y :'a t),
  card (union X Y) <= card(X) + card(Y).

lemma union_card1 : forall (X:'a t, Y:'a t),
 card (union X Y) <= card (X) + card(Y)
proof.
 intros X.
 cut H : (P_union_card1 X).
 apply Set_ind<:'a>(P_union_card1,_,_,X);trivial.
 trivial.
save.

pred P_union_card2( Y : 'a t) = forall(X:'a t),
 card X <= card (union X Y).

lemma union_card2 : forall (Y:'a t, X:'a t),
 card X <= card (union X Y)
proof. 
 intros Y.
 cut H : (P_union_card2 Y).
 apply Set_ind<:'a>(P_union_card2,_,_,Y). 
 trivial.
 intros S x H H1.
 cut H0 : (forall(X:'a t),
 card X <= card (union X (add x S))).
 intros X.
 cut H2: (card X <= card (union X S)).
 trivial.
 cut H3: (card (union X S) <= card (union X (add x S))).
 cut H4: (card (union X (add x S)) = card (add x (union X S))).
 trivial.
 trivial.
 trivial.
 trivial.
 trivial.
save.


  (* subset card *)

lemma susbset_card : forall (Y : 'a t, X : 'a t),
 X <= Y => (card X) <= (card Y)
proof.
 intros Y X H.
 cut H0: (exists (Z : 'a t), Y = union X Z).
 trivial.
 elim H0.
 intros Z H1.
 cut H2: (card X <= card (union X Z)).
 trivial.
 trivial.
save.

  (* intersection *)
axiom inter_mem : forall(X:'a t, Y:'a t, x: 'a),
 mem x (inter X Y) <=> (mem x X && mem x Y).

lemma inter_empty : forall(X :'a t),
inter X empty = empty
proof.
 intros X.
 cut H : (inter X empty == empty).
 trivial.
 trivial.
save.

lemma inter_comm : forall(X:'a t, Y:'a t),
inter X Y = inter Y X 
proof.
 intros X Y.
 cut H: (inter X Y == inter Y X).
 trivial.
 trivial.
save.

lemma inter_add : forall(X:'a t, Y:'a t, x: 'a),
add x (inter X Y) = inter (add x X) (add x Y)
proof.
 intros X Y x;cut ext_eq: (add x (inter X Y) == inter (add x X) (add x Y)).
   cut H: (forall y, mem y (add x (inter X Y)) = mem y (inter (add x X) (add x Y)));trivial.
 trivial.
save.

lemma inter_add2 :forall(X : 'a t, Y : 'a t, x : 'a),
mem x Y =>
add x (inter X Y) = inter (add x X)  Y
proof.
 intros X Y x H.
 cut H0: (add x (inter X Y) == inter (add x X)  Y).
 trivial.
 trivial.
save.


lemma inter_add3 :forall(X : 'a t, Y : 'a t, x : 'a),
 !mem x Y =>
(inter X Y) = inter (add x X)  Y
proof.
 intros X Y x H.
 cut H0: ((inter X Y) == inter (add x X)  Y).
 trivial.
 trivial.
save.

lemma subset_inter : forall (X Y : 'a t),
 inter X Y <= X.

lemma card_inter : forall (X Y : 'a t),
 card (inter X Y) <= card X.

pred P_union_inter(X: 'a t) = forall(Y : 'a t),
 card(union X Y) + card(inter X Y) = card(X) + card(Y).

lemma card_union_inter : forall (X Y: 'a t),
 card(union X Y) + card(inter X Y) = card(X) + card(Y)
proof. 
 intros X.
 cut H: (P_union_inter X).
 apply Set_ind<:'a>(P_union_inter,_,_, X).
 trivial.
 intros S x H H0.
 cut H1 : (forall (Y : 'a t),
 card(union (add x S) Y) + card(inter (add  x S) Y) = card(add x S) + card(Y)).
 intros Y.
 cut H8: (card(union S Y) + card(inter S Y) = card(S) + card(Y)).
 trivial.
 cut H2 : (mem x Y =>
 card(union (add x S) Y) + card(inter (add  x S) Y) = card(add x S) + card(Y)).
 intros H3.
 cut H4: (card (add x (inter S Y)) = card(inter (add x S) Y)).
 cut H5: (add x (inter S Y) = (inter (add x S) Y)).
 trivial.
 trivial.
 cut H5: (!mem x (inter S Y)).
 trivial.
 cut H6 : (card(inter (add  x S) Y) = 1 + card (inter S Y)).
 trivial.
 cut H7: (card(add x S) = 1 + card S).
 trivial.
 trivial.
 cut H3 : (!mem x Y =>
 card(union (add x S) Y) + card(inter (add  x S) Y) = card(add x S) + card(Y)).
 intros H4.
 cut H5: (card (inter S Y) = card(inter (add x S) Y)).
 trivial.
 cut H6: (!mem x (union S Y)).
 trivial.
 cut H7: (card(union(add x S) Y) = 1 + card(union S Y)).
 trivial.
 trivial.
 trivial.
 trivial.
 trivial.
save.