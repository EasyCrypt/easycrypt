abstract theory GroupAction.

require import Group.

type group.
type set. (* Is this finite? *)
clone include Group with type group <- group.

op act : group -> set -> set.

axiom id (x : set) : act e x = x.
axiom comp (g h : group) (x : set) : act (g * h) x = act g (act h x).

(* -------------------------------------------------------------------- *)

op faith (g : group) = injective (act g).
op trans (x y : set) = exists (g : group), act g x = y.
op free (g h : group) = (exists (x : set), act g x = act h x) => g = h.
op reg (x y : set) (g h : group) = (trans x y) /\ (free g h).

(* -------------------------------------------------------------------- *)

lemma cancel (g : group) (x y : set) : act g x = act g y => x = y.
proof.
move=> /(congr1 (act (inv g))).
rewrite -!comp.
rewrite !mulVc.
by rewrite !id.
qed.

lemma com (g h : group) (x : set) : g \com h => act g (act h x) = act h (act g x).
proof.
move=> ghcom.
rewrite -!comp.
by rewrite ghcom.
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
require import FinType.

clone include GroupAction.

clone FinType with
  type t <- group.

op sample : group distr.
op x0 : set.

end EGA.


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

clone FinType with
  type t <- group.

op x0 : set.
op actgens (x : set) : (set * set) list.

end REGA.

(* -------------------------------------------------------------------- *)
  (* Hardness assumptions for (R)EGAs *)

require import List DList Distr FinType.

clone include GroupAction.
clone MFinite as Dg with type t <- group.
clone MFinite as X with type t <- set.

op group_dist = Dg.dunifin. 
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
module type Adv_Wu = {
  proc solve (ts : (set * set) list, x : set) : set
}.


module Wu (A: Adv_Wu) = {
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
module type Adv_Wp = {
  proc solve (ts : (set * set) list) : bool
}.

module Wu_real (A : Adv_Wp) = {
  proc main (n : int) : bool = {
    var g, ts, b;
    g <$ group_dist;
    (* [(x, act g x) : x <$ set_dist, i \in [n]] *)
    ts <$ dmap (dlist set_dist n) (map (fun x => (x, act g x)));
    b <@ A.solve(ts);
    return b;
  }
}.

module Wu_ideal (A : Adv_Wp) = {
  proc main (n : int) : bool = {
    var ts, b;
    ts <$ dlist (set_dist `*` set_dist) n; (* [(x, u) : x, u <$ set_dist, i \in [n]] *)
    b <@ A.solve(ts);
    return b;
  }
}.

