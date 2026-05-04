require import Int.

(* ==================================================================== *)
(* Abstract monoid: where all the lemmas live, written once.            *)
(* ==================================================================== *)
type class monoid = {
  op idm : monoid
  op (+) : monoid -> monoid -> monoid

  axiom addmA : associative (+)
  axiom addmC : commutative (+)
  axiom add0m : left_id idm (+)
}.

(* -------------------------------------------------------------------- *)
section.
declare type t <: monoid.

lemma addm0: right_id idm<:t> (+).
proof. by move=> x; rewrite addmC add0m. qed.

lemma addmCA: left_commutative (+)<:t>.
proof. by move=> x y z; rewrite !addmA (addmC x). qed.

lemma addmAC: right_commutative (+)<:t>.
proof. by move=> x y z; rewrite -!addmA (addmC y). qed.

lemma addmACA: interchange (+)<:t> (+).
proof. by move=> x y z t; rewrite -!addmA (addmCA y). qed.

lemma iteropE n (x : t): iterop n (+) x idm = iter n ((+) x) idm.
proof.
elim/natcase n => [n le0_n|n ge0_n].
+ by rewrite ?(iter0, iterop0).
+ by rewrite iterSr // addm0 iteropS.
qed.
end section.

(* ==================================================================== *)
(* Flavor tags: empty subclasses of monoid. They carry no extra
   structure; their only purpose is to drive display (\sum vs \prod
   for bigops, [zero]/[+] vs [one]/[*] for the operators).               *)
(* ==================================================================== *)
type class addmonoid <: monoid = {}.

type class mulmonoid <: monoid = {}.

(* -------------------------------------------------------------------- *)
(* Source-level renamings on top of [monoid]'s operators. Each abbrev is
   a transparent alias; it parses to the underlying monoid op and prints
   back as the alias when the type carries the matching flavor tag.     *)
(* -------------------------------------------------------------------- *)
abbrev zero ['a <: addmonoid] : 'a = idm<:'a>.

abbrev one ['a <: mulmonoid] : 'a = idm<:'a>.

abbrev ( * ) ['a <: mulmonoid] (x y : 'a) = (+)<:'a> x y.
