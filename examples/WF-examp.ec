(* example use of well-founded recursion and induction
   (theories/structures/WF.ec) *)

require import AllCore List IntDiv StdOrder.
import IntOrder.

require import WF.

(* define well-founded relation on lists: lt_list_size xs ys <=>
   size xs < size ys *)

op lt_list_size : 'a list rel = wf_pre size lt_nat.

lemma wf_lt_list_size ['a] : wf lt_list_size<:'a>.
proof.
rewrite wf_pre wf_lt_nat.
qed.

lemma lt_list_sizeP (xs ys : 'a list) :
  lt_list_size xs ys <=> size xs < size ys.
proof.
by rewrite /lt_list_size /wf_pre /lt_nat size_ge0.
qed.

(* body of well-founded recursive definition that "chunkifies" an 'a
   list into an 'a list list: the first n elements, then the next n
   elements, etc., where if at the end there are < n elements left,
   they are discarded *)

op chunkify_wf_rec_def (n : int) : ('a list, 'a list list) wf_rec_def =
  fun (xs : 'a list,                     (* input list *)
       f : 'a list -> 'a list list) =>   (* for recursive calls on
                                            strictly shorter lists *)
  if n <= size xs
  then take n xs :: f (drop n xs)
  else [].

(* the actual recursive definition: *)

op chunkify (n : int) : 'a list -> 'a list list =
  wf_recur
  lt_list_size              (* well-founded relation being used *)
  []                        (* element to be returned if recursive calls
                               don't respect well-founded relation *)
  (chunkify_wf_rec_def n).  (* body of recursive definition *)

lemma chunkify_size (n : int, xs : 'a list) :
  1 <= n => size (chunkify n xs) = size xs %/ n.
proof.
move => ge1_n; move : xs.
apply (wf_ind lt_list_size).  (* use well-founded induction on lt_list_size *)
apply wf_lt_list_size.
rewrite /chunkify => /= xs IH.
rewrite wf_recur 1:wf_lt_list_size.
rewrite {1}/chunkify_wf_rec_def.  (* only need to rewrite at top-level *)
case (n <= size xs) => [le_n_size_xs | not_le_n_size_xs].
(* first case *)
rewrite lt_list_sizeP.
have lt_size_drop : size (drop n xs) < size xs by rewrite size_drop /#.
rewrite lt_size_drop /= IH 1:lt_list_sizeP //.
rewrite size_drop 1:/# ler_maxr 1:/#.
have {2}-> : size xs = n + (size xs - n) by smt().
rewrite (divzDl n) 1:dvdzz divzz /#.
(* second case *)
smt(size_ge0 ltr_normr).
qed.
