require import Logic.
require import Int.
require import Fun.

(* For this specification, almost everything is axiomatized.
   This is a prime candidate for 1) realization, and 2) refinement types. *)

type 'a set.

(* These will all be axiomatized *)
op empty : 'a set.
op add   : 'a -> 'a set -> 'a set.
op pick  : 'a set -> 'a.
op rm    : 'a -> 'a set -> 'a set.
op union : 'a set -> 'a set -> 'a set.
op inter : 'a set -> 'a set -> 'a set.
op mem   : 'a -> 'a set -> bool.
op card  : 'a set -> int.

(* Derived operators and predicates *)
op singleton (x:'a) : 'a set = add x empty.
op is_empty (X:'a set) : bool = X = empty.
op cPmem X (x:'a) = mem x X.

(* "Induction Principle" *)
axiom Set_ind: forall (P:('a set) cPred),
  P empty =>
  (forall x S, !mem x S => P S => P (add x S)) =>
  forall S, P S.

(* Extentional Equality *)
pred (==) (X1 X2:'a set) = forall (x:'a),
  mem x X1 <=> mem x X2.

lemma eq_refl: forall (X:'a set), X == X by [].

lemma eq_sym: forall (X Y:'a set), X == Y => Y == X by [].

lemma eq_trans: forall (X Y Z:'a set),
  X == Y => Y == Z => X == Z
by [].

axiom extensionality: forall (X1 X2:'a set),
  X1 == X2 => X1 = X2.

(* Subset *)
pred (<=) (X1 X2:'a set) = forall x,
  mem x X1 => mem x X2.

lemma sub_refl: forall (X:'a set), X <= X by [].

lemma sub_anti_sym: forall (X Y:'a set),
  X <= Y => Y <= X => X == Y
by [].

lemma sub_trans: forall (X Y Z:'a set),
  X <= Y => Y <= Z => X <= Z
by [].

(** Specification of operators *)
(* empty *)
axiom empty_mem: forall (x:'a), !mem x empty.

lemma empty_subset: forall (X:'a set), empty <= X by [].

(* add *)
axiom add_mem: forall (x y:'a) X, 
  mem x (add y X) <=> mem x X \/ x = y.

axiom add_card: forall (x:'a) X, 
  !mem x X => card (add x X) = card X + 1.

lemma mem_add: forall (x:'a) X,
  mem x X => X = add x X.
proof.
intros x X x_in_X;
  apply (extensionality<:'a>  X (add x X) _);
  trivial.
save.

lemma add_subset: forall (x:'a) X,
  X <= add x X
by [].

(* card *)
axiom card_empty: card<:'a> empty = 0.
axiom card_rm: forall (x:'a) S, mem x S => card S = 1 + card(rm x S).

pred (* local *) cP_card_pos (X:'a set) = 0 <= card X.
lemma card_pos: forall (X:'a set), 0 <= card X.
proof.
intros X;cut IH: (cP_card_pos X);
[ apply (Set_ind<:'a> cP_card_pos _ _ X);trivial |
  trivial ].
save.

(* singleton *)
lemma singleton_card: forall (x:'a),
  card (singleton x) = 1
by [].

(* filter *)
op filter: 'a cPred -> 'a set -> 'a set.

axiom filter_mem: forall (x:'a) P X,
  mem x (filter P X) <=> (mem x X /\ P x).

axiom filter_card: forall (P:'a cPred) X, 
  card (filter P X) = card X - card (filter (cPnot P) X). 

axiom filter_cPeq_in: forall (x:'a) X,
  mem x X => filter (cPeq x) X = singleton x.

axiom filter_cPeq_card_in : forall (x:'a) X,
  mem x X => card (filter (cPeq x) X) = 1.

lemma filter_subset: forall (P:'a cPred) X,
 filter P X <= X
by [].

(* pick *)
axiom pick_spec: forall (X:'a set), 
  X <> empty => mem (pick X) X.

lemma pick_singleton: forall (x:'a), 
  pick (singleton x) = x
by [].

(* rm *)
axiom rm_spec_not_mem: forall (x:'a) X,
  !mem x X => rm x X = X.

axiom rm_spec_mem: forall (x:'a) X,
  mem x X => add x (rm x X) = X.

axiom rm_mem: forall (x:'a) X,
  !mem x (rm x X).

lemma rm_subs: forall (x:'a) X,
  rm x X <= X
by [].

lemma rm_card: forall (x:'a) X,
  card(rm x X) <= card X
by [].

lemma card_non_empty: forall (x:'a) X,
  mem x X => card X = 1 + card (rm x X)
by [].

pred (* local *) cP_is_empty_card(X:'a set) = card X = 0 => is_empty X.
lemma is_empty_card: forall (X:'a set),
  card X = 0 => is_empty X. 
proof.
intros X;cut IH: (cP_is_empty_card X);
[ apply (Set_ind<:'a> cP_is_empty_card _ _ X); trivial |
  trivial ].
save.

(* union *) 
axiom union_mem: forall (x:'a) X Y,
  mem x (union X Y) <=> (mem x X \/ mem x Y).

lemma union_empty: forall (X:'a set),
  union X empty = X.
proof.
intros X;
  apply (extensionality<:'a> (union X empty) X _);
  trivial.
save.

lemma union_comm: forall (X Y:'a set),
  union X Y = union Y X.
proof.
intros X Y;
  apply (extensionality<:'a> (union X Y) (union Y X) _).
  intros x;trivial.
save.

lemma union_add: forall (x:'a) X Y,
  add x (union X Y) = union (add x X) Y.
proof.
 intros x X Y.
  apply (extensionality<:'a> (add x (union X Y)) (union (add x X) Y) _).
  intros y;trivial.
save.

lemma subset_union1: forall (X Y:'a set),
  X <= union X Y
by [].

pred (* local *) cP_subset_union(X:'a set) = forall Y,
  X <= Y => exists Z, Y = union X Z.

lemma subset_union2: forall (X Y:'a set),
  X <= Y => exists Z, Y = union X Z.
proof.
intros X;cut H0: (cP_subset_union X).
  apply (Set_ind<:'a> cP_subset_union _ _ X).
    trivial.
    intros x S H H0;cut H1: (forall Y, (add x S) <= Y => (exists Z, Y = union (add x S) Z)).
      intros Y H1;cut H2 : (S <= Y).
        trivial.
        cut H3: (forall Y, S <= Y => exists Z, Y = union S Z).
          trivial.
          cut H4: (exists Z, Y = union S Z).
            apply (H3 Y _);assumption.
            elim H4;intros Z H5;trivial.
      trivial.
  trivial.
save.

pred (* local *) cP_union_card1(X:'a set) = forall Y,
  card (union X Y) <= card(X) + card(Y).
lemma union_card1: forall (X Y:'a set),
  card (union X Y) <= card (X) + card(Y).
proof.
intros X;cut H: (cP_union_card1 X);
[ apply (Set_ind<:'a> cP_union_card1 _ _ X); trivial |
  trivial ].
save.

pred (* local *) cP_union_card2(Y:'a set) = forall (X:'a set),
  card X <= card (union X Y).
lemma union_card2: forall (Y X:'a set),
  card X <= card (union X Y).
proof. 
intros Y;cut H: (cP_union_card2 Y).
  apply (Set_ind<:'a> cP_union_card2 _ _ Y). 
    trivial.
    intros x S H H1;cut H0 : (forall X, card X <= card (union X (add x S))).
      intros X;cut H2: (card X <= card (union X S)).
        trivial.
        cut H3: (card (union X S) <= card (union X (add x S))).
          cut H4: (card (union X (add x S)) = card (add x (union X S)));trivial.
          trivial.
      trivial.
    trivial.
save.

lemma subset_card: forall (X Y:'a set),
  X <= Y => (card X) <= (card Y).
proof.
intros X Y H;cut H0: (exists Z, Y = union X Z).
  trivial.
  elim H0;intros Z H1;cut H2: (card X <= card (union X Z));
    trivial.
save.

(* intersection *)
axiom inter_mem: forall (x:'a) X Y,
  mem x (inter X Y) <=> (mem x X /\ mem x Y).

lemma inter_empty: forall (X:'a set),
  inter X empty = empty.
proof.
intros X;
  apply (extensionality<:'a> (inter X empty) empty _);
  trivial.
save.

lemma inter_comm: forall (X Y:'a set),
  inter X Y = inter Y X.
proof.
intros X Y;
  apply (extensionality<:'a> (inter X Y) (inter Y X) _);
  trivial.
save.

lemma inter_add: forall (x:'a) X Y,
  add x (inter X Y) = inter (add x X) (add x Y).
proof.
intros x X Y;
  apply (extensionality<:'a> (add x (inter X Y)) (inter (add x X) (add x Y)) _);
  cut ext: (forall y, mem y (add x (inter X Y)) = mem y (inter (add x X) (add x Y)));trivial.
save.

lemma inter_add2: forall (x:'a) X Y,
  mem x Y => add x (inter X Y) = inter (add x X)  Y.
proof.
intros x X Y x_in_Y;
  apply (extensionality<:'a> (add x (inter X Y)) (inter (add x X)  Y) _);
  trivial.
save.

lemma inter_add3: forall (x:'a) X Y,
  !mem x Y => (inter X Y) = inter (add x X) Y.
proof.
intros x X Y x_nin_Y;
  apply (extensionality<:'a> (inter X Y) (inter (add x X) Y) _);
  trivial.
save.

lemma subset_inter: forall (X Y:'a set),
  inter X Y <= X
by [].

lemma card_inter: forall (X Y:'a set),
  card (inter X Y) <= card X
by [].

pred (*local *) cP_union_inter(X:'a set) = forall Y,
  card (union X Y) + card (inter X Y) = card X + card Y.

lemma card_union_inter: forall (X Y:'a set),
  card (union X Y) + card (inter X Y) = card X + card Y.
proof. 
intros X;cut IH: (cP_union_inter X).
  apply (Set_ind<:'a> cP_union_inter _ _  X).
    trivial.
    intros x S H H0;cut H1: (forall Y, card (union (add x S) Y) + card (inter (add x S) Y) =
                                         card (add x S) + card Y).
      intros Y;cut H8: (card (union S Y) + card (inter S Y) = card S + card Y).
        trivial.
        cut H2: (mem x Y => card(union (add x S) Y) + card (inter (add x S) Y) = card (add x S) + card Y).
          intros H3;cut H4: (card (add x (inter S Y)) = card (inter (add x S) Y)).
            cut H5: (add x (inter S Y) = (inter (add x S) Y));trivial.
            cut H5: (!mem x (inter S Y)).
              trivial.
              cut H6: (card (inter (add x S) Y) = 1 + card (inter S Y)).
                trivial.
                cut H7: (card (add x S) = 1 + card S);trivial.
          cut H3: (!mem x Y => card (union (add x S) Y) + card (inter (add x S) Y) =
                                 card (add x S) + card Y).
            intros H4;cut H5: (card (inter S Y) = card (inter (add x S) Y)).
              trivial.
              cut H6: (!mem x (union S Y)).
                trivial.
                cut H7: (card (union (add x S) Y) = 1 + card (union S Y));trivial.
      trivial.
    trivial.
  trivial.
save.

require import Real.
require import Distr.

(* Uniform distribution on a (finite) set *)
theory Duni.
  op duni: 'a set -> 'a distr.

  axiom supp_def: forall (x:'a) X, in_supp x (duni X) <=> mem x X.

  axiom mu_def: forall (X:'a set) P, 
    !is_empty X =>
       mu (duni X) P = (card (filter P X))%r / (card X)%r. 

  axiom mu_def_empty: forall (P:'a cPred), 
      mu (duni empty) P = 0%r.

  axiom mu_x_def_in: forall (x:'a) X, 
    mem x X => mu_x (duni X) x = 1%r / (card X)%r. 

  axiom mu_x_def_nin: forall (x:'a) X, 
    !mem x X => mu_x (duni X) x = 0%r.

  axiom mu_weight: forall (X:'a set), 
     !is_empty X => mu_weight (duni X) = 1%r.

end Duni.

(* Restriction of a distribution (sub-distribution) *)
theory Drestr.
  op drestr: 'a distr -> 'a set -> 'a distr.
 
  axiom supp_def: forall (x:'a) d X, 
     in_supp x (drestr d X) <=> in_supp x d /\ !mem x X.
  
  axiom mu_x_def_notin: forall (x:'a) d X, 
    in_supp x d => !mem x X =>
    mu_x (drestr d X) x = mu_x d x.

  axiom mu_x_def_in: forall (x:'a) d X, 
    in_supp x d => mem x X =>
    mu_x (drestr d X) x = 0%r.

  axiom mu_weight: forall (d:'a distr) X, 
    mu_weight (drestr d X) = mu_weight d - mu d (cPmem X).
end Drestr.

(* Scaled Restriction of a Distribution *)
theory Dexcepted.
  op (\) (d:'a distr,X:'a set): 'a distr =
    Dscale.dscale (Drestr.drestr d X). 

  lemma supp_def: forall (x:'a) d X,
     (in_supp x (d \ X) => (in_supp x d /\ !mem x X)) /\
     ((in_supp x d /\ !mem x X) => in_supp x (d \ X)).
  proof.
  intros d X x;split.
    intros in_supp;split;trivial.
    intros in_supp_nmem;trivial.
  save.
    
  lemma mu_x_def: forall (x:'a) d X,
     mu_x (d \ X) x = (in_supp x (d \ X)) ? mu_x d x / (mu_weight d - mu d (cPmem X)) : 0%r
  by [].

  lemma mu_weight_def: forall (d:'a distr) X,
    mu_weight (d \ X) = (mu_weight d = mu d (cPmem X)) ? 0%r : 1%r
  by [].
end Dexcepted.
