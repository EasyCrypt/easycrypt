(* prod split + intro. *)
require import AllCore Distr DBool DProd.

module N = {
  var x : bool
  var y : bool
  proc sample_tuple() : bool = {
    (N.x, N.y) <$ {0,1} `*` {0,1};
    return N.x;
  }
  proc noop() : bool = { return N.x; }
}.

(* Fire prod split on a tuple-lvalue product sample in R. *)
lemma prod_split_fires :
  equiv[ N.sample_tuple ~ N.noop : true ==> true ].
proof.
proc. delay.
dcoupl pop {1} 1.
(* R_l: (N.x, N.y) <$ {0,1} `*` {0,1} *)
dcoupl prod {1}.
(* R_l becomes: N.x <$ {0,1}; N.y <$ {0,1} *)
admit.
qed.

(* Round-trip: prod split then prod intro gives back the original. *)
lemma prod_split_intro_roundtrip :
  equiv[ N.sample_tuple ~ N.noop : true ==> true ].
proof.
proc. delay.
dcoupl pop {1} 1.
dcoupl prod {1}.
dcoupl prod intro {1}.
admit.
qed.
