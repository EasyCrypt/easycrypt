require import AllCore Int Real Xreal.

module M = {
  proc main_int(x : int) = {
    return x; 
  }

  proc main_bool(x : bool) = {
    return x; 
  }
}.

lemma L &m (_x : int):
  Pr [ M.main_int(_x) @ &m : _x = res ] <= 1%r.
proof.
byehoare (_: ((arg = _x) `|` (1%xr)) ==> _) => //.
- proc; auto => &hr.
  by apply xle_cxr_r => ->.
qed.

lemma L1 (&m: {arg: bool}): !arg{m} =>
  Pr [ M.main_bool(true) @ &m : true] <= 0%r.
proof.
move => arg_eq.
byehoare (_: (!arg{m})%xr ==> _).
+ proc; auto. by rewrite arg_eq.
fail by auto.
abort.
