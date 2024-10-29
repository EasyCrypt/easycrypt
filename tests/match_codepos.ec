(* -------------------------------------------------------------------- *)
require import Distr.

(* -------------------------------------------------------------------- *)
module M = {
  proc f(x : bool option) = {
    var y;
    y <- false; 
    match x with
    | None => {}
    | Some v => {
      if (v) {
        y <$ dunit ((y || true) && true);
      }
    }
    end;
    return y;
  }
  proc g(x : bool option) = {
    var z;
    z <- false; 
    match x with
    | None => {}
    | Some v => {
      if (v) {
        z <$ dunit true;
      }
    }
    end;
    return z;
  }
}.

(* -------------------------------------------------------------------- *)
equiv l: M.f ~ M.g: ={arg} ==> ={res}.
proof.
proc.
proc rewrite {1} ^match#Some.^if.^y<$ /=.
by sim.
qed.
