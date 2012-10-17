
op o : () -> int.

print o.

pop po : () -> int.

print po.

adversary A() : unit { () -> int; unit -> unit}.

game G = {
  var z : int

  fun f'() : int = { return 0; }

  fun f''(u:unit) : unit = { return u; }

  abs A = A {f',f''}

  fun f() : unit = { z = o (); }
  
  fun g() : unit = {
    var u : unit;
    f'' (u);
    f();
  }
}
.


print G.

