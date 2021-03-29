(* --------------------------------------------------------------------
 * Copyright (c) - 2021-2021 - Boston University
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* An axiom-free formalization of well-founded relations, induction
   and recursion.

   Makes no use of smt. *)

require import AllCore StdOrder.
import IntOrder.

(* ------------- predicates, expanding on prelude/Logic.ec ------------ *)

type 'a predi = 'a -> bool.

(* if pr : 'a predi and x : 'a, then we read "pr x" as "x satisfies
   pr"; we can think of predicates as representing sets - the elements
   they map to true *)

op is_empty (xs : 'a predi) : bool = forall (y : 'a), ! xs y.

op is_nonempty (xs : 'a predi) : bool = ! is_empty xs.

lemma is_nonempty (xs : 'a predi) :
  is_nonempty xs <=> exists (y : 'a), xs y.
proof.
rewrite /is_nonempty /is_empty.
by rewrite negb_forall.
qed.

op sub (xs ys : 'a predi) : bool =
  forall (z : 'a), xs z => ys z.

lemma sub_trans (zs xs ys : 'a predi) :
  sub xs zs => sub zs ys => sub xs ys.
proof.
rewrite /sub => sub_xs_zs sub_zs_ys z xs_z.
by rewrite sub_zs_ys sub_xs_zs.
qed.

(* ----------------------------- relations ---------------------------- *)

(* the type of relations is defined in prelude/Logic.ec as

     type 'a rel = 'a -> 'a -> bool.

   if rel : 'a rel and x, y : 'a, then we read "rel x y" as "the pair
   (x, y) is in rel" *)

(* ---------------------- well-founded relations ---------------------- *)

op wf (rel : 'a rel) : bool =
  forall (xs : 'a predi),
  is_nonempty xs =>
  exists (x : 'a), xs x /\ ! exists (y : 'a), xs y /\ rel y x.

(* predecessors of x in rel *)

op predecs (rel : 'a rel, x : 'a) : 'a predi =
  fun y => rel y x.

(* ----------- induction principle on well-founded relations ---------- *)

lemma wf_ind (rel : 'a rel, P : 'a -> bool) :
  wf rel =>
  (forall (x : 'a),
   (forall (y : 'a), rel y x => P y) =>
   P x) =>
  (forall (x : 'a), P x).
proof.
move => wf_rel H.
case (forall x, P x) => //.
rewrite negb_forall => [[z not_P_z]].
have [x [#] not_P_x not_ex] := wf_rel (predC P) _.
  rewrite is_nonempty.
  by exists z.
have P_x : P x.
  apply (H x) => y rel_y_x.
  case (P y) => [// | not_P_y].
  have // : exists y, predC P y /\ rel y x.
    by exists y.
by rewrite /predC in not_P_x.
qed.

(* ---------------- constructing well-founded relations --------------- *)

(* restriction of Int.(<) to natural numbers *)

op lt_nat (x y : int) = 0 <= x < y.

lemma wf_lt_nat : wf lt_nat.
proof.  
move => xs is_ne_xs.
have H :
  forall n,
  0 <= n => xs n =>
  exists x, xs x /\ ! exists y, xs y /\ lt_nat y x.
  apply sintind => i ge0_i IH xs_i.
  case (exists y, xs y /\ lt_nat y i) =>
    [[y [#] xs_y] | not_ex].
  rewrite /lt_nat => [[ge0_y lt_y_i]].
  by apply (IH y).
  by exists i.
have [x xs_x] : exists x, xs x.
  by apply is_nonempty.
case (0 <= x) => [ge0_x | lt0_x].
by apply (H x).
rewrite -ltzNge in lt0_x.
exists x; split => //.
case (exists y, xs y /\ lt_nat y x) => [[y [xs_y]] | //].
rewrite /lt_nat => [[ge0_y lt_y_x]].
have lt0_y : y < 0.
  by rewrite (ltz_trans x).
have // : y < y.
  by rewrite (ltr_le_trans 0).
qed.

(* lexicographic orderings *)

op wf_lex (wfr1 : 'a rel, wfr2 : 'b rel) : ('a * 'b) rel =
  fun (p1 p2 : 'a * 'b) =>
  wfr1 p1.`1 p2.`1 \/ (p1.`1 = p2.`1 /\ wfr2 p1.`2 p2.`2).

lemma wf_lex (wfr1 : 'a rel, wfr2 : 'b rel) :
  wf wfr1 => wf wfr2 => wf (wf_lex wfr1 wfr2).
proof.
move => wf_wfr1 wf_wfr2.
rewrite /wf_lex /wf => xs /is_nonempty [x xs_x].
have [y1 [] /= [y [xs_y y1_eq]] not_y1_pred]
     := wf_wfr1 (fun y1 => exists p, xs p /\ p.`1 = y1) _.
  rewrite /is_nonempty /is_empty negb_forall /=.
  by exists x.`1; exists x.
rewrite negb_exists /= in not_y1_pred.
have [z2 [] /= [z [xs_z [z1_eq z2_eq]]] not_z2_pred]
     := wf_wfr2
        (fun z2 =>
         exists (p : 'a * 'b), xs p /\ p.`1 = y1 /\ p.`2 = z2) _.
  rewrite /is_nonempty /is_empty negb_forall /=.
  by exists y.`2; exists y.
rewrite negb_exists /= in not_z2_pred.
exists z.
rewrite xs_z /=.
case (exists y0,
      xs y0 /\ (wfr1 y0.`1 z.`1 \/ y0.`1 = z.`1 /\ wfr2 y0.`2 z.`2)) =>
  // [[p] [xs_p [wfr1_p1_z1 | [eq_p1_z1 wfr2_p2_z2]]]].
have contrad : (exists p', xs p' /\ p'.`1 = p.`1) /\ wfr1 p.`1 y1.
  split.
  exists p; by rewrite xs_p.
  by rewrite -z1_eq.
have // := not_y1_pred p.`1.
have contrad :
     (exists (p' : 'a * 'b), xs p' /\ p'.`1 = y1 /\ p'.`2 = p.`2) /\
     wfr2 p.`2 z2.
  split.
  exists p; by rewrite xs_p eq_p1_z1 z1_eq.
  rewrite -z2_eq wfr2_p2_z2.
have // := not_z2_pred p.`2.
qed.

(* restrictions of well-founded relations *)

op wf_restr (wfr : 'a rel, rel : 'a rel) : 'a rel =
  fun (x : 'a, y : 'a) => wfr x y /\ rel x y.

lemma wf_restr (wfr : 'a rel, rel : 'a rel) :
  wf wfr => wf (wf_restr wfr rel).
proof.
move => wf_wfr.
rewrite /wf /wf_restr => xs ne_xs.
have [x [xs_x not_ex_x_pred]] := wf_wfr xs _.
  trivial.
exists x.
rewrite xs_x /=.
case (exists y, xs y /\ wfr y x /\ rel y x) =>
  [[y [#] xs_y wfr_y_x rel_y_x] | //].
have // : exists y, xs y /\ wfr y x.
by exists y.
qed.

(* precomposing well-founded relation with function *)

op wf_pre (f : 'a -> 'b, wfr : 'b rel) : 'a rel =
  fun (x : 'a, y : 'a) => wfr (f x) (f y).

lemma wf_pre (f : 'a -> 'b, wfr : 'b rel) :
  wf wfr => wf (wf_pre f wfr).
proof.
move => wf_wfr.
rewrite /wf /wf_pre => xs.
rewrite /is_nonempty /is_empty negb_forall => /= [[x xs_x]].
have [y /= [[x' [xs_x' <-]] not_ex_f_x'_pred]]
     := (wf_wfr (fun y => exists x, xs x /\ f x = y) _).
  rewrite /is_nonempty /is_empty negb_forall /=.
  by exists (f x); exists x.
exists x'.
rewrite xs_x' /=.
case (exists x'', xs x'' /\ wfr (f x'') (f x')) =>
  [[x'' [xs_x'' wfr_f_x''_f_x']] | //].
have // :
  exists y', (exists x'', xs x'' /\ f x'' = y') /\ wfr y' (f x').
  exists (f x'').
  rewrite wfr_f_x''_f_x' /=.
  by exists x''.
qed.

(* ---------------------- well-founded recursion ---------------------- *)

(* if you just want to *use* well-founded recursion, skip ahead to
   definitions of wf_rec_def and wf_recur *)

(* generalized relations *)

type ('a, 'b) grel = 'a -> 'b -> bool.

op grel0 : ('a, 'b) grel =  (* empty relation *)
  fun (x : 'a, y : 'b) => false.

op grelT : ('a, 'b) grel =  (* relation with all elements *)
  fun (x : 'a, y : 'b) => true.

op grel_sub (r1 r2 : ('a, 'b) grel) : bool =
  forall (x : 'a, y : 'b), r1 x y => r2 x y.

lemma grel_sub_trans (grel' grel1 grel2 : ('a, 'b) grel) :
  grel_sub grel1 grel' => grel_sub grel' grel2 => grel_sub grel1 grel2.
proof.
rewrite /grel_sub => sub_grel1_grel' sub_grel'_grel2 x y grel1_x_y.
by rewrite sub_grel'_grel2 sub_grel1_grel'.
qed.

op grel_dom (grel : ('a, 'b) grel) : 'a predi =
  fun (x : 'a) => exists (y : 'b), grel x y.

op grel_rng (grel : ('a, 'b) grel) : 'b predi =
  fun (y : 'b) => exists (x : 'a), grel x y.

op grel_is_fun (grel : ('a, 'b) grel) : bool =
  forall (x : 'a, y z : 'b), grel x y => grel x z => y = z.

lemma grel_eq_same_dom (grel1 grel2 : ('a, 'b) grel, xs : 'a predi) :
  grel_dom grel1 = xs => grel_dom grel2 = xs =>
  (forall (x : 'a), xs x => grel1 x = grel2 x) =>
  grel1 = grel2.
proof.
move => dom_grel1_xs dom_grel2_xs grel1_grel2_agree_dom.
apply fun_ext => x.
case (xs x) => [xs_x | not_xs_x].
by apply grel1_grel2_agree_dom.
have @/grel_dom not_grel1_x : ! grel_dom grel1 x.
  by rewrite dom_grel1_xs.
have @/grel_dom not_grel2_x : ! grel_dom grel2 x.
  by rewrite dom_grel2_xs.
apply fun_ext => y.
have -> : grel1 x y = false.
  case (grel1 x y) => [grel1_x_y | //].
  have // : exists y, grel1 x y.
    by exists y.
have -> // : grel2 x y = false.
  case (grel2 x y) => [grel2_x_y | //].
  have // : exists y, grel2 x y.
    by exists y.
qed.

lemma grel_funs_eq_on_first (grel1 grel2 : ('a, 'b) grel, x : 'a, y : 'b) :
  grel_is_fun grel1 => grel_is_fun grel2 =>
  grel1 x y => grel2 x y => grel1 x = grel2 x.
proof.
move => is_fun_grel1 is_fun_grel2 grel1_x_y grel2_x_y.
apply fun_ext => y'.
case (y' = y) => [-> | ne_y'_y].
by rewrite grel1_x_y grel2_x_y.
have -> : grel1 x y' = false.
  case (grel1 x y') => [grel1_x_y' | //].
  have // : y' = y.
    by apply (is_fun_grel1 x).
have -> // : grel2 x y' = false.
  case (grel2 x y') => [grel2_x_y' | //].
  have // : y' = y.
    by apply (is_fun_grel2 x).
qed.

op grel_restr (grel : ('a, 'b) grel, xs : 'a predi) : ('a, 'b) grel =
  fun (x : 'a) => if xs x then grel x else fun (y : 'b) => false.

lemma grel_restr (grel : ('a, 'b) grel, xs : 'a predi) :
  sub xs (grel_dom grel) =>
  grel_dom (grel_restr grel xs) = xs /\
  (forall (x : 'a, y : 'b),
   grel_restr grel xs x y <=>
   grel x y /\ xs x).
proof.
rewrite /sub /grel_restr /grel_dom => sub_xs_dom_grel.
split => [| x y].
rewrite fun_ext => x.
rewrite eqboolP.
case (xs x) => [xs_x | //].
by rewrite sub_xs_dom_grel.
by case (xs x).
qed.

lemma grel_restr_grel_sub (grel : ('a, 'b) grel, xs : 'a predi) :
  grel_sub (grel_restr grel xs) grel.
proof.
rewrite /grel_sub /grel_restr => x y.
by case (xs x).
qed.

lemma grel_restr_dom (grel : ('a, 'b) grel, xs : 'a predi) :
  sub xs (grel_dom grel) =>
  grel_dom (grel_restr grel xs) = xs.
proof.
move => sub_xs_dom_grel.
have // := grel_restr grel xs _.
  trivial.
qed.

lemma grel_restr_is_fun (grel : ('a, 'b) grel, xs : 'a predi) :
  sub xs (grel_dom grel) => grel_is_fun grel =>
  grel_is_fun (grel_restr grel xs).
proof.
move => sub_xs_dom_grel grel_is_fun_grel.
rewrite /grel_is_fun /grel_restr => x y z.
case (xs x) => [xs_x | //].
apply grel_is_fun_grel.
qed.

op grel_to_fun (def : 'b, grel : ('a, 'b) grel) : 'a -> 'b =
  fun (x : 'a) => choiceb (grel x) def.

op grel_choose_sub_fun (grel : ('a, 'b) grel) : ('a, 'b) grel =
  fun (x : 'a, y : 'b) =>
  grel_dom grel x /\ y = choiceb (grel x) witness.

lemma grel_choose_sub_fun (grel : ('a, 'b) grel) :
  let grel' = grel_choose_sub_fun grel in
  grel_is_fun grel' /\ grel_sub grel' grel /\
  grel_dom grel' = grel_dom grel.
proof.
rewrite /=.
split.
by rewrite /grel_choose_sub_fun /grel_is_fun => x y z.
split.
rewrite /grel_choose_sub_fun /grel_sub => x y [dom_grel_x ->].
by apply (choicebP (grel x)).
rewrite /grel_choose_sub_fun /grel_dom fun_ext => x.
rewrite eqboolP.
split => [[y [] -> //] | [y grel_x_y]].
exists (choiceb (grel x) witness).
split; [by exists y | trivial].
qed.

lemma grel_exists_sub_fun (grel : ('a, 'b) grel, xs : 'a predi) :
  sub xs (grel_dom grel) =>
  exists (grel' : ('a, 'b) grel),
  grel_sub grel' grel /\ grel_is_fun grel' /\ grel_dom grel' = xs.
proof.
move => sub_xs_dom_grel.
exists (grel_restr (grel_choose_sub_fun grel) xs).
have /= [#] is_fun_choose_grel sub_choose_grel_grel dom_eq_choose_grel_grel
       := grel_choose_sub_fun grel.
split.
rewrite (grel_sub_trans (grel_choose_sub_fun grel))
        1:(grel_restr_grel_sub (grel_choose_sub_fun grel)).
have /= [#] _ -> // := (grel_choose_sub_fun grel).
split.
by rewrite (grel_restr_is_fun (grel_choose_sub_fun grel))
           1:dom_eq_choose_grel_grel.
by rewrite grel_restr_dom 1:dom_eq_choose_grel_grel.
qed.

type ('a, 'b) grels = ('a, 'b) grel predi.  (* represents set of grels *)

(* generalized intersection

   the intersection of the empty grels is the universal relation,
   which exists because we are working in a typed setting *)

op grels_inter (grels : ('a, 'b) grels) : ('a, 'b) grel =
  fun (x : 'a, y : 'b) =>
    forall (grel : ('a, 'b) grel), grels grel => grel x y.

lemma grels_inter_sub (grels : ('a, 'b) grels, grel : ('a, 'b) grel) :
  grels grel => grel_sub (grels_inter grels) grel.
proof.
move => grels_grel.
rewrite /grel_sub => x y.
rewrite /grels_inter => all_x_y.
by apply all_x_y.
qed.

(* body of well-founded recursive definition: given an input (x : 'a)
   and a function (f : 'a -> 'b) for doing recursive calls, produce an
   answer of type 'b *)

type ('a, 'b) wf_rec_def = 'a -> ('a -> 'b) -> 'b.

(* when grel is closed with respect to a well-founded relation wfr, a
   default element def, and a body wfrd of a recursive definition

   the default element is returned if wfrd calls (grel_to_fun def
   grel') on a value not in the domain of grel', i.e., one that is
   not a predecessor of x in wfr *)

op wf_closed
   (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def,
    grel : ('a, 'b) grel) : bool =
  forall (x : 'a, grel' : ('a, 'b) grel),
  grel_sub grel' grel => grel_is_fun grel' =>
  grel_dom grel' = predecs wfr x =>
  grel x (wfrd x (grel_to_fun def grel')).

lemma wfc_total
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def,
       grel : ('a, 'b) grel, x : 'a) :
  wf wfr => wf_closed wfr def wfrd grel => grel_dom grel x.
proof.
move => wf_wfr wfc_grel.
move : x.
apply (wf_ind wfr) => //= x IH.
have [grel' [#] sub_grel'_grel is_fun_grel' dom_grel'_eq_preds_x]
       := grel_exists_sub_fun grel (predecs wfr x) _.
  apply IH.
have grel_x_witness := wfc_grel x grel' _ _ _; first 3 trivial.
by exists (wfrd x (grel_to_fun def grel')).
qed.

lemma wfc_inter
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def,
       grels : ('a, 'b) grels) :
  (forall (grel : ('a, 'b) grel),
   grels grel => wf_closed wfr def wfrd grel) =>
  wf_closed wfr def wfrd (grels_inter grels).
proof.
rewrite /wf_closed =>
  all_closed x grel' grel'_sub_inter is_fun_grel' dom_grel'_preds.
rewrite /grels_inter in grel'_sub_inter.
rewrite /grels_inter => grel grels_grel.
rewrite all_closed // /grel_sub => x' y' grel'_x'_y'.
by rewrite grel'_sub_inter.
qed.

(* this is our candidate for the recursively defined function, as a
   grel: the intersection of the set of all closed grels *)

op wfc_least
   (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) : ('a, 'b) grel =
  grels_inter (wf_closed wfr def wfrd).

lemma wfc_least_closed
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) :
  wf_closed wfr def wfrd (wfc_least wfr def wfrd).
proof.
by rewrite /wfc_least wfc_inter.
qed.

lemma wfc_least_total
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def, x : 'a) :
  wf wfr => grel_dom (wfc_least wfr def wfrd) x.
proof.
move => wf_wfr.
rewrite (wfc_total wfr def wfrd) // wfc_least_closed.
qed.

lemma wfc_least_dom_predT
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) :
  wf wfr => grel_dom (wfc_least wfr def wfrd) = predT.
proof.
move => wf_wfr.
apply fun_ext => x.
by rewrite wfc_least_total.
qed.

lemma wfc_least_least
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def,
       grel : ('a, 'b) grel) :
  wf_closed wfr def wfrd grel =>
  grel_sub (wfc_least wfr def wfrd) grel.
proof.
rewrite /wfc_least => grel_closed.
by apply grels_inter_sub.
qed.

op wfc_least_char_aux
   (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) : ('a, 'b) grel =
 fun (x : 'a, y : 'b) =>
   wfc_least wfr def wfrd x y /\
    exists (grel' : ('a, 'b) grel),
    grel_sub grel' (wfc_least wfr def wfrd) /\ grel_is_fun grel' /\
    grel_dom grel' = predecs wfr x /\ y = wfrd x (grel_to_fun def grel').

lemma wfc_least_char
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def,
       x : 'a, y : 'b) :
  wfc_least wfr def wfrd x y =>
  exists (grel' : ('a, 'b) grel),
  grel_sub grel' (wfc_least wfr def wfrd) /\ grel_is_fun grel' /\
  grel_dom grel' = predecs wfr x /\ y = wfrd x (grel_to_fun def grel').
proof.
have aux_closed :
     wf_closed wfr def wfrd (wfc_least_char_aux wfr def wfrd).
  rewrite /wf_closed =>
    x' grel' sub_grel'_aux is_fun_grel' dom_grel'_preds_x.
  rewrite /wfc_least_char_aux.
  have sub_grel'_least : grel_sub grel' (wfc_least wfr def wfrd).
    rewrite (grel_sub_trans (wfc_least_char_aux wfr def wfrd)) //
            /wfc_least_char_aux => x'' y'' //.
  split.
  by apply wfc_least_closed.
  by exists grel'.
move => least_x_y.
have @/wfc_least_char_aux [_ ->] // :
     wfc_least_char_aux wfr def wfrd x y.
  by rewrite (wfc_least_least wfr def wfrd
              (wfc_least_char_aux wfr def wfrd)).
qed.

op wfc_least_is_fun_aux
   (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) : ('a, 'b) grel =
 fun (x : 'a, y : 'b) =>
   wfc_least wfr def wfrd x y /\
   forall (z : 'b), wfc_least wfr def wfrd x z => y = z.

lemma wfc_least_is_fun
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) :
  grel_is_fun (wfc_least wfr def wfrd).
proof.
have aux_closed :
     wf_closed wfr def wfrd (wfc_least_is_fun_aux wfr def wfrd).
  rewrite /wf_closed =>
    x' grel' grel'_sub_aux is_fun_grel' dom_grel'_preds_x'.
  rewrite /wfc_least_is_fun_aux.
  have sub_grel'_least : grel_sub grel' (wfc_least wfr def wfrd).
    by rewrite (grel_sub_trans (wfc_least_is_fun_aux wfr def wfrd)) //
               /wfc_least_is_fun_aux => x'' y''.
  have -> /= z' least_x'_z' :
       wfc_least wfr def wfrd x' (wfrd x' (grel_to_fun def grel')).
    by apply wfc_least_closed.    
  have [grel'' [#] sub_grel''_least is_fun_grel''
        dom_grel''_preds_x' ->]
       := wfc_least_char wfr def wfrd x' z' _.
    trivial.
  congr; congr.
  rewrite (grel_eq_same_dom grel' grel'' (predecs wfr x')) // =>
    a preds_wfr_x'_a.
  have @/grel_dom [b grel'_a_b] : grel_dom grel' a.
    by rewrite dom_grel'_preds_x'.
  have @/grel_dom [b' grel''_a_b']: grel_dom grel'' a.
    by rewrite dom_grel''_preds_x'.
  have @/wfc_least_is_fun_aux [_ least_a_uniq_b] := grel'_sub_aux a b _.
    trivial.
  have least_a_b' := sub_grel''_least a b' _.
    trivial.
  have eq_b_b' := least_a_uniq_b b' _.
    trivial.
  move : grel''_a_b'; rewrite -eq_b_b'; move => grel''_a_b.
  by apply (grel_funs_eq_on_first grel' grel'' a b).
rewrite /grel_is_fun => x y z least_x_y least_x_z.
have @/wfc_least_is_fun_aux [_ least_x_uniq_y] :
     wfc_least_is_fun_aux wfr def wfrd x y.
  by rewrite (wfc_least_least wfr def wfrd
              (wfc_least_is_fun_aux wfr def wfrd)).
  by apply least_x_uniq_y.
qed.

lemma wfc_least_result
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def, x : 'a) :
  wf wfr =>
  wfc_least wfr def wfrd x
  (wfrd x
        (grel_to_fun def
         (grel_restr (wfc_least wfr def wfrd) (predecs wfr x)))).
proof.
move => wf_wfr.
apply (wfc_least_closed wfr def wfrd x
       (grel_restr (wfc_least wfr def wfrd) (predecs wfr x))).
apply grel_restr_grel_sub.
apply grel_restr_is_fun.
by rewrite wfc_least_dom_predT.
apply wfc_least_is_fun.
by rewrite grel_restr_dom 1:wfc_least_dom_predT.
qed.

(* well-founded recursion operator - smt solvers treat as black box,
   but can use wf_recur lemma *)

op nosmt wf_recur
   (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def) : 'a -> 'b =
  grel_to_fun def (wfc_least wfr def wfrd).

lemma choiceb_grel_fun (grel : ('a, 'b) grel, x : 'a, y, def : 'b) :
  grel_is_fun grel => grel x y => choiceb (grel x) def = y.
proof.
move => grel_is_fun_grel grel_x_y.
have grel_x_choice_grel_x := choicebP (grel x) def _.
  by exists y.
by apply (grel_is_fun_grel x).
qed.

(* the recursion lemma *)

lemma wf_recur
      (wfr : 'a rel, def : 'b, wfrd : ('a, 'b) wf_rec_def, x : 'a) :
  wf wfr =>
  wf_recur wfr def wfrd x =
  wfrd x
       (fun y =>
          if wfr y x
          then wf_recur wfr def wfrd y
          else def).
proof.
move => wf_wfr.
rewrite /wf_recur /grel_to_fun.
apply (choiceb_grel_fun (wfc_least wfr def wfrd) x).
apply wfc_least_is_fun.
have least_result := wfc_least_result wfr def wfrd x _.
  trivial.
have -> :
  (fun (y : 'a) =>
   if wfr y x then choiceb (wfc_least wfr def wfrd y) def
   else def) =
  (grel_to_fun def (grel_restr (wfc_least wfr def wfrd) (predecs wfr x))).
  rewrite /grel_to_fun.
  apply fun_ext => y.
  case (wfr y x) => [wfr_y_x | not_wfr_y_x].
  by rewrite /grel_restr /predecs wfr_y_x.
  by rewrite eq_sym choiceb_dfl /grel_restr /predecs 1:not_wfr_y_x.
rewrite least_result.
qed.
