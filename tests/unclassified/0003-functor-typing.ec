module type I = {
  var x:bool
}.

module M(I:I): I = {
  var x:bool
  fun init():unit = {
    x = I.x;
  }
}.