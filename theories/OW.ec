(* Trapdoor one-way permutations *)
require import Distr.

(** Abstract declarations to be refined when instantiating *)
(* Support *)
type t.

(* Keys *)
type pkey.
type skey.
op keypairs: (pkey * skey) distr.
axiom keypairsL: weight keypairs = 1%r.

(* The distribution from which the challenge is sampled *)
(* Note: We use its support as the permutation's domain! *)
op challenge: pkey -> t distr.
axiom challengeL pk: weight (challenge pk) = 1%r.
axiom challengeU pk: isuniform (challenge pk).

(** Concrete definitions *)
pred valid_keys (ks:pkey * skey) = in_supp ks keypairs.
pred valid_pkey (pk:pkey) = exists sk, valid_keys (pk,sk).
pred valid_skey (sk:skey) = exists pk, valid_keys (pk,sk).

op f: pkey -> t -> t.
pred f_dom (pk:pkey) (x:t) =
  support (challenge pk) x.
pred f_rng (pk:pkey) (y:t) =
  exists x, f_dom pk x /\ y = f pk x.

op finv: skey -> t -> t.
axiom finv_correct (pk:pkey) (sk:skey) y:
  valid_keys (pk,sk) =>
  f_rng pk y =>
  f_dom pk (finv sk y).

axiom finvof (pk:pkey) (sk:skey) (x:t):
  valid_keys (pk,sk) =>
  f_dom pk x =>
  finv sk (f pk x) = x.

axiom fofinv (pk:pkey) (sk:skey) (x:t):
  valid_keys (pk,sk) =>
  f_rng pk x =>
  f pk (finv sk x) = x.

(* This is often useful to extract plaintexts *)
lemma f_pk_inj (x, y:t) (pk:pkey) (sk:skey):
  valid_keys (pk,sk) =>
  f_dom pk x => f_dom pk y =>
  f pk x = f pk y => x = y.
proof strict.
by intros=> Hsupp Hdom_x Hdom_y Heqf;
   rewrite -(finvof pk sk) // -(finvof pk sk y) // Heqf.
qed.

module type Inverter = {
  fun invert(pk : pkey, y : t) : t
}.

module OW(I :Inverter) ={
  fun main(): bool ={
    var x,x':t;
    var pk:pkey;
    var sk:skey;

    (pk,sk) = $keypairs;
    x       = $challenge pk;
    x'      = I.invert(pk,f pk x);
    return (x = x');
  }
}.
