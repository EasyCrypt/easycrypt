require import AllCore.

op w : unit option.

module M = {
  proc f() = {
    match w with
    | None => {}
    | Some y => {}
    end;
  }
}.

hoare L1: M.f: exists x, x = true ==> true.
proof.
proc.
match.
+ by skip.
+ by skip.
qed.

phoare L2: [M.f: exists x, x = true ==> true] <= 1%r.
proof.
proc.
match.
+ by skip.
+ by skip.
qed.

phoare L3: [M.f: exists x, x = true ==> true] = 1%r.
proof.
proc.
match.
+ by skip.
+ by skip.
qed.

phoare L4: [M.f: exists x, x = true ==> true] >= 1%r.
proof.
proc.
match.
+ by skip.
+ by skip.
qed.

equiv L5: M.f ~ M.f: exists x, x = true ==> true.
proof.
proc.
match {1}.
+ match {2}.
  + by skip.
  + by skip.
+ match {2}.
  + by skip.
  + by skip.
qed.
