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
    var x : gf_q;
    var y : gf_q;
    var d : bool;

    x  = $Dgf_q.dgf_q;
    y  = $Dgf_q.dgf_q;

    return (g^x, g^y, g^(x*y));
  }

  fun sample_random() : group * group * group = {
    var x : gf_q;
    var y : gf_q;
    var z : gf_q;
    var d : bool;

    x  = $Dgf_q.dgf_q;
    y  = $Dgf_q.dgf_q;
    z  = $Dgf_q.dgf_q;

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
