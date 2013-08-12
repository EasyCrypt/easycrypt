(* Trapdoor one-way permutations *)
require import Distr.

type t.

type pkey.
type skey.
op keypairs: (pkey * skey) distr.
axiom keypairsL: mu keypairs cpTrue = 1%r.

op f: pkey -> t -> t.
op f_dom: pkey -> t -> bool.
op f_rng: pkey -> t -> bool.

op finv: skey -> t -> t.
op finv_dom: skey -> t -> bool.
op finv_rng: skey -> t -> bool.

axiom f_rng_sub_finv_dom pk sk:
  in_supp (pk,sk) keypairs =>
  f_rng pk <= finv_dom sk.

axiom finv_rng_sub_f_dom pk sk:
  in_supp (pk,sk) keypairs =>
  finv_rng sk <= f_dom pk.

axiom finvof (pk:pkey) (sk:skey) (x:t):
  in_supp (pk,sk) keypairs =>
  f_dom pk x =>
  finv sk (f pk x) = x.

axiom fofinv (pk:pkey) (sk:skey) (x:t):
  in_supp (pk,sk) keypairs =>
  finv_dom sk x =>
  f pk (finv sk x) = x.

(* This is often useful to extract plaintexts *)
lemma f_pk_inj (x, y:t) (pk:pkey) (sk:skey):
  in_supp (pk,sk) keypairs  =>
  f_dom pk x => f_dom pk y =>
  f pk x = f pk y => x = y.
proof.
by intros=> Hsupp Hdom_x Hdom_y Heqf;
   rewrite -(finvof pk sk _ _) // -(finvof pk sk y _) // Heqf.
qed.

(* This is bad. *)
op sample_t: t distr. 

axiom f_dom_sample_t pk:
  mu sample_t (f_dom pk) = mu sample_t cpTrue.

module type Inverter = {
  fun inverter(pk : pkey, y : t) : t
}.

module OW(I :Inverter) ={
  var pk:pkey
  fun main() : bool ={
    var x,x',y : t;
    var sk : skey;

    x       = $sample_t;
    (pk,sk) = $keypairs;
    x'      = I.inverter(pk,(f pk x));
    return (x = x');
  }
}.