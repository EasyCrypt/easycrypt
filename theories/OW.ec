(* Trapdoor one-way permutations *)
require import Distr.

type t.

type pkey.
type skey.
op keypairs: (pkey * skey) distr.
axiom keypairsL: weight keypairs = 1%r.

pred valid_keys (ks:pkey * skey) = in_supp ks keypairs.
pred valid_pkey (pk:pkey) = exists sk, valid_keys (pk,sk).
pred valid_skey (sk:skey) = exists pk, valid_keys (pk,sk).

op f: pkey -> t -> t.
op f_dom: pkey -> t -> bool.
op f_rng: pkey -> t -> bool.

op finv: skey -> t -> t.
op finv_dom: skey -> t -> bool.
op finv_rng: skey -> t -> bool.

axiom f_rng_finv_dom pk sk:
  valid_keys (pk,sk) =>
  f_rng pk = finv_dom sk.

axiom finv_rng_f_dom pk sk:
  valid_keys (pk,sk) =>
  finv_rng sk = f_dom pk.

axiom f_f_rng pk x:
  valid_pkey pk =>
  f_dom pk x =>
  f_rng pk (f pk x).

axiom f_finv_rng sk x:
  valid_skey sk =>
  finv_dom sk x =>
  finv_rng sk (finv sk x).

axiom finvof (pk:pkey) (sk:skey) (x:t):
  valid_keys (pk,sk) =>
  f_dom pk x =>
  finv sk (f pk x) = x.

axiom fofinv (pk:pkey) (sk:skey) (x:t):
  valid_keys (pk,sk) =>
  finv_dom sk x =>
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

(* Distribution on the plaintexts *)
op challenge: pkey -> t distr.
axiom f_dom_challenge pk:
  mu (challenge pk) (f_dom pk) = 1%r.

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
