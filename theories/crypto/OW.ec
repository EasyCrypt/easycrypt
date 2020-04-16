(* --------------------------------------------------------------------
 * Copyright (c) - 2012--2016 - IMDEA Software Institute
 * Copyright (c) - 2012--2018 - Inria
 * Copyright (c) - 2012--2018 - Ecole Polytechnique
 *
 * Distributed under the terms of the CeCILL-B-V1 license
 * -------------------------------------------------------------------- *)

(* One-Way Trapdoor Permutations *)
require import Core Distr.

(** Abstract declarations to be refined when instantiating *)
(* Domain and Range *)
type D, R.

(* Keys *)
type pkey, skey.

op dkeys: (pkey * skey) distr.
axiom dkeys_ll: is_lossless dkeys.

pred valid_keys (ks:pkey * skey) = support dkeys ks.
pred valid_pkey (pk:pkey) = exists sk, valid_keys (pk,sk).
pred valid_skey (sk:skey) = exists pk, valid_keys (pk,sk).

(* The distribution from which the challenge is sampled *)
(* Note: We use its support as the permutation's domain! *)
op challenge: pkey -> D distr.

axiom challenge_ll pk:
  valid_pkey pk => is_lossless (challenge pk).

axiom challenge_uni pk:
  valid_pkey pk => is_uniform (challenge pk).

(** Concrete definitions *)
op f: pkey -> D -> R.

pred f_dom (pk:pkey) (x:D) =
  valid_pkey pk => x \in (challenge pk).

pred f_rng (pk:pkey) (y:R) =
  valid_pkey pk => exists x, f_dom pk x /\ y = f pk x.

op finv: skey -> R -> D.

axiom finv_correct (pk:pkey) (sk:skey) y:
  valid_keys (pk,sk) =>
  f_rng pk y =>
  f_dom pk (finv sk y).

axiom finvof (pk:pkey) (sk:skey) (x:D):
  valid_keys (pk,sk) =>
  f_dom pk x =>
  finv sk (f pk x) = x.

axiom fofinv (pk:pkey) (sk:skey) (x:R):
  valid_keys (pk,sk) =>
  f_rng pk x =>
  f pk (finv sk x) = x.

(* This is often useful to extract plaintexts *)
lemma f_pk_inj (x, y:D) (pk:pkey) (sk:skey):
  valid_keys (pk,sk) =>
  f_dom pk x => f_dom pk y =>
  f pk x = f pk y => x = y.
proof.
by move=> Hsupp Hdom_x Hdom_y Heqf;
   rewrite -(finvof pk sk) // -(finvof pk sk y) // Heqf.
qed.

(** We can now define the module types and modules that define security **)
module type Inverter = {
  proc invert(pk : pkey, y : R) : D
}.

module OW(I :Inverter) ={
  proc main(): bool ={
    var x,x':D;
    var pk:pkey;
    var sk:skey;

    (pk,sk) <$ dkeys;
    x       <$ challenge pk;
    x'      <@ I.invert(pk,f pk x);
    return (x = x');
  }
}.
