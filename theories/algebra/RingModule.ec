(* ==================================================================== *)
require import AllCore List Ring Int SubRing Bigalg.
require (*--*) Bigop.


(* ==================================================================== *)
abstract theory ComRingModule.
  type scalar, t.

  clone import ComRing as CRScalar with
    type t <= scalar.
  clone import ZModule as ZMod with
    type t <= t.

  op ( ** ) : scalar -> t -> t.

  axiom scaleDl (x y : scalar) (a : t) : (x + y) ** a = x ** a + y ** a.
  axiom scaleDr (x : scalar) (a b : t) : x ** (a + b) = x ** a + x ** b.
  axiom scaleM (x y : scalar) (a : t) : (x * y) ** a = x ** (y ** a).
  axiom scale1r (a : t) : oner ** a = a.

  clone import BigZModule as BigZMod with
    theory ZM <- ZMod.

  abbrev lin ss vs : t =
    big predT idfun (map (fun (x : scalar * t) => fst x ** snd x) (zip ss vs)).

  op free vs  = forall ss , size ss = size vs => lin ss vs = ZMod.zeror => ss = nseq (size vs) CRScalar.zeror.
  op gen vs v = exists ss , size ss = size vs /\ lin ss vs = v.
  op gent vs  = forall v , gen vs v.
  op basis vs = (free vs) /\ (gent vs).

  lemma free_nil :
    free [].
  proof. by move => ss /= /size_eq0 ->> /=; rewrite nseq0. qed.

  lemma free_uniq vs :
    free vs =>
    uniq vs.
  proof.
    admit.
  qed.

  lemma free_incl vs1 vs2 :
    (mem vs1 <= mem vs2) =>
    free vs2 =>
    free vs1.
  proof.
    move => mem_incl free2 ss.
    admit.
  qed.

  lemma gen_incl vs1 vs2 :
    (mem vs1 <= mem vs2) =>
    gent vs1 =>
    gent vs2.
  proof.
    move => mem_incl free1 v.
    admit.
  qed.

  lemma free_cons v vs :
    free (v :: vs) <=> (!(gen vs v) /\ free vs).
  proof.
    admit.
  qed.

  lemma gen_cons v w vs :
    gen (v :: vs) w <=> (exists x a , w = x ** v + a /\ gen vs a).
  proof.
    admit.
  qed.
end ComRingModule.

(* -------------------------------------------------------------------- *)
abstract theory IDomainModule.
  type scalar, t.

  clone import IDomain as IDScalar with type t <= scalar.

  clone include ComRingModule with
    type scalar     <- scalar,
    type t          <- t,
    theory CRScalar <- IDScalar.
end IDomainModule.

(* -------------------------------------------------------------------- *)
abstract theory VectorSpace.
  type scalar, t.

  clone import Field as FScalar with type t <= scalar.

  clone include IDomainModule with
    type scalar     <- scalar,
    type t          <- t,
    theory IDScalar <- FScalar.
end VectorSpace.


(* ==================================================================== *)
abstract theory SubComRingModule.
  type t, st.

  clone import ComRing as CR with
    type t <= t.

  clone import SubComRing
    with type t <= t,
    type st <= st,
    theory CR <- CR.

  import Sub.

  op ( ** ) (x : st) (a : t) : t =
    val x * a.

  clone ComRingModule with
    type scalar     <- st,
    type t          <- t,
    theory CRScalar <- SubComRing.SCR,
    theory ZMod     <- CR,
    op     ( ** )   <- ( ** )
    proof *.

  realize scaleDl.
  proof. by move=> x y a; rewrite /( ** ) valD mulrDl. qed.

  realize scaleDr.
  proof. by move => x a b; rewrite /( ** ) mulrDr. qed.

  realize scaleM .
  proof. by move => x y a; rewrite /( ** ) valM mulrA. qed.

  realize scale1r.
  proof. by move => a; rewrite /( ** ) val1 mul1r. qed.
end SubComRingModule.

(* -------------------------------------------------------------------- *)
abstract theory SubIDomainModule.
  type t, st.

  clone import IDomain as ID with
    type t <= t.

  clone include SubComRingModule with
    type t    <- t,
    type st   <- st,
    theory CR <- ID.
end SubIDomainModule.

(* -------------------------------------------------------------------- *)
abstract theory SubVectorSpace.
  type t, st.

  clone import Field as F with
    type t <= t.

  clone include SubIDomainModule with
    type t    <- t,
    type st   <- st,
    theory ID <- F.
end SubVectorSpace.
