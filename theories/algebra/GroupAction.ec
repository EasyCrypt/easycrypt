abstract theory GroupAction.

require import Group AllCore.

type group.
type set.
clone include Group with
  type group <- group.

op act : group -> set -> set.

axiom id (x : set) : act e x = x.
axiom comp (g h : group) (x : set) : act (g * h) x = act g (act h x).

(* -------------------------------------------------------------------- *)
op faith (g h : group) = g <> h => exists (x :set), act g x <> act h x.
op trans (x y : set) = exists (g : group), act g x = y.

op free (g h : group) = (exists (x : set), act g x = act h x) => g = h.
op free2 (g : group) = (exists (x : set), act g x = x) => g = e.

op reg (x y : set) (g h : group) = (trans x y) /\ (free g h).

op extract (x y : set) = choiceb (fun g => act g x = y) e.

(* -------------------------------------------------------------------- *)
lemma extractK (x y : set) : trans x y => act (extract x y) x = y.
proof.
move=> /choicebP /=.
apply.
qed.

lemma actgI (g : group) : injective (act g).
proof.
move=> x y /(congr1 (act (inv g))).
rewrite -!comp.
rewrite !mulVc.
by rewrite !id.
qed.
    
lemma actC1 (g h : group) (x : set) : g \com h => act g (act h x) = act h (act g x).
proof.
move=> ghcom.
rewrite -!comp.
by rewrite ghcom.
qed.

lemma freeEquiv : (forall (g h : group), free g h) <=> (forall (g : group), free2 g).
proof.
split.
+ move=> fr g s.
  apply (fr g e).
  elim s.
  move=> x ac.
  exists x.
  by rewrite id.
move=> fr g h s.
print right_injective.
apply (mulcI (inv h)).
rewrite mulVc.
apply fr.
elim s.
move=> x ac.
exists x.
by rewrite comp ac -comp mulVc id.
qed.

end GroupAction.

(* -------------------------------------------------------------------- *)
(* Definining properties for an Effective Group Action (EGA), G -> X -> X. 

G is finite and there are efficient algorithms for:
  - Membership testing.
  - Equality testing.
  - Sampling, statistically close to uniform.
  - Computing g * h for any g, h \in G.
  - Computing inv g for any g \in G. 
  
X needs:
  - membership testing for a bit string.
  - a canonical string representation that represents any given x \in X.

Exists a unique x_0 \in X (origin), with a known bit string reprentation.

Efficient algorithm that computes (act g x) for any x, g \in X.
*)

theory EGA.
require import FinType Distr.

clone include GroupAction.

clone FinType as G with
  type t <- group.

clone FinType as X with
  type t <- set.
  
clone MFinite as DG with
  type t <- group.

op sample = DG.dunifin.
op x0 : set.

end EGA.

(* Abelian Regular EGA *)
theory ARegEGA.

clone include EGA.

clone import Group.ComGroup as CG with
    type group <- group,
      op     e <- e,
      op ( * ) <- ( * ).
print CG.

(* just reg
axiom regP (x y : set) (g h : group) : reg x y g h.
*)

(* both free and trans *)
axiom transP (x y : set) : trans x y.
axiom freeP (g h : group) : free g h.


(* ---------------------------------- *)
lemma actC (g h : group) (x : set) : act g (act h x) = act h (act g x).
proof.
apply (actC1 g h x).
exact mulcC.
qed.

lemma extractP (x y : set) : act (extract x y) x = y.
proof.
apply extractK.
exact transP.
qed.

(* Maybe prove this in GroupAction with assumption of freeness *)
lemma extractUniq (x : set) (g : group) : g = extract x (act g x).
proof.
apply freeP.
exists x.
by rewrite extractP.
qed.

(* Alternate formulation, not sure if needed *)
lemma extractUniq2 (x y : set) (g h : group) : g = extract x y /\ h = extract x y => g = h.
proof.
case=> eqg eqh.
apply freeP.
by subst.
qed.

end ARegEGA.

(* Definining properties for an REGA, G -> X -> X, 

G = <Ggen> = <{g_1, ..., g_n}>.

G is finite and n = O(x^(log|G|)).

X finite and need:
   - membership testing for a bit string.
   - a canonical string representation that represents any given x \in X.

Exists a unique x_0 \in X (origin), with a known bit string representation. 

Efficient algorithm that computes (act g_i x) and (act (G.inv g_i) x) for any x \in X.
*)

theory REGA.
require import FinType List.
clone include GroupAction.

clone FinType as G with
  type t <- group.

clone FinType as X with
  type t <- set.
  
op x0 : set.
op actgens (x : set) : (set * set) list.

end REGA.

(* -------------------------------------------------------------------- *)
(* Hardness assumptions for (R)EGAs *)

require import List DList Distr FinType.

clone include GroupAction.
clone MFinite as GD with type t <- group.
clone MFinite as X with type t <- set.

op group_dist = GD.dunifin. 
op set_dist = X.dunifin.

(* One Wayness *)
module type Adv_OW = {
  proc solve (x y : set) : group
}.

module OW (A: Adv_OW) = {
  proc main (): bool = {
    var x, gc, g;

    x <$ set_dist;
    gc <$ group_dist;
    g <@ A.solve(x, act gc x);
    return g = gc;
  }
}.

(* Weak Unpredictability *)
module type Adv_WUP = {
  proc solve (ts : (set * set) list, x : set) : set
}.


module Wu (A: Adv_WUP) = {
  proc main (n : int) : bool = {
    var g, ts, xc, yc, y;

    g <$ group_dist;
    (* [(x, act g x) : x <$ set_dist, i \in [n]] *)
    ts <$ dmap (dlist set_dist n) (map (fun x => (x, act g x)));
    xc <$ set_dist;
    yc <- act g xc;
    y <@ A.solve(ts, xc);
    return y = yc;
  }
}.

(* Weak pseudorandomness *)
module type Adv_WPR = {
  proc solve (ts : (set * set) list) : bool
}.

module WPR_real (A : Adv_WPR) = {
  proc main (n : int) : bool = {
    var g, ts, b;
    g <$ group_dist;
    (* [(x, act g x) : x <$ set_dist, i \in [n]] *)
    ts <$ dmap (dlist set_dist n) (map (fun x => (x, act g x)));
    b <@ A.solve(ts);
    return b;
  }
}.

module WPR_ideal (A : Adv_WPR) = {
  proc main (n : int) : bool = {
    var ts, b;
    ts <$ dlist (set_dist `*` set_dist) n; (* [(x, u) : x, u <$ set_dist, i \in [n]] *)
    b <@ A.solve(ts);
    return b;
  }
}.

