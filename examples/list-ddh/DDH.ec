require import Int.
require import Bool.
require import Prime_field.
require import Cyclic_group_prime.

module type DDH_DISTINGUISHER = { 
  fun dist(X Y Z : group) : bool
}.

op a = Dgf_q.dgf_q.

(* sampling dh-triples and random-triples *)
module DH_distrs = {
  fun sample_dh() : group * group * group = {
    var xi : int;
    var yi : int;
    var x : gf_q;
    var y : gf_q;
    var d : bool;

    xi = $[0..q-1];
    yi = $[0..q-1];
    x  = $Dgf_q.dgf_q;
    y  = i_to_gf_q(yi);

    return (g^x, g^y, g^(x*y));
  }

  fun sample_random() : group * group * group = {
    var xi : int;
    var yi : int;
    var zi : int;
    var x : gf_q;
    var y : gf_q;
    var z : gf_q;
    var d : bool;

    xi = $[0..q-1];
    yi = $[0..q-1];
    zi = $[0..q-1];
    x  = i_to_gf_q(xi);
    y  = i_to_gf_q(yi);
    z  = i_to_gf_q(zi);

    return (g^x, g^y, g^z);
  }
}.

module DDH0 (D:DDH_DISTINGUISHER) = { 
  fun main() : bool = {
    var X : group;
    var Y : group;
    var Z : group;
    var b : bool;

    (X,Y,Z) := DH_distrs.sample_dh();
    b := D.dist(X,Y,Z);
    
    return b;
  }     
}.


module DDH1 (D:DDH_DISTINGUISHER) = { 
  fun main() : bool = {
    var X : group;
    var Y : group;
    var Z : group;
    var b : bool;

    (X,Y,Z) := DH_distrs.sample_random();
    b := D.dist(X,Y,Z);
    
    return b;
  }
}.
