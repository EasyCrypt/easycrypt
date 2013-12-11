module type I = {
  proc init():unit 
}.

module M(I:I): I = {
  var x:bool
  proc init():unit = {
    I.init();
    x = true;
  }
}.
