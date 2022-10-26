module F = {
  proc f () = {
    var r;

    r <- 0;
  }

  proc g () = {
    var s;

    s <- 1;
  }
}.

module G = {
  proc f () = {
    var t;

    F.g();
    t <- 2;
  }

  proc g () = {
    var u;

    F.f();
    u <- 3;
  }
}.

module Game = {
  proc main () = {
    F.f();
    G.g();
    F.g();
    G.f();
  }
}.

equiv inline_full_procedures : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline F.f G.g.
admitted.

equiv inline_star : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline *.
admitted.

equiv inline_blank : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline.
admitted.

equiv inline_module : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline F.
admitted.

equiv inline_procedure : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline f.
admitted.

equiv inline_minus_full_procedure : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline * - F.f.
admitted.

equiv inline_minus_procedure : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline * - f.
admitted.

equiv inline_minus_module : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline * - F.
admitted.

equiv inline_minuses : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline * - F - g.
admitted.

equiv inline_add_back : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline * - F F.
admitted.

equiv inline_remove_back : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline F - F.
admitted.

equiv inline_side : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline{1} *.
admitted.

equiv inline_occs : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline{1} (1 4).
admitted.

equiv inline_occs_pat : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline{1} (1 2) * - G.
admitted.

equiv inline_codepos : Game.main ~ Game.main : true ==> true.
proof.
proc.
inline {1} 3.
admitted.
