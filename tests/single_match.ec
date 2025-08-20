op w : unit option.

module M = {
  proc f() = {
    match w with
    | None => {}
    | Some y => {}
    end;
  }
}.

hoare L: M.f: exists x, x = true ==> true.
proof.
proc.
match.
+ by skip.
+ by skip.
qed.
