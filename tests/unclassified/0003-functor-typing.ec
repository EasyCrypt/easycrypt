module type I = {
  fun init():unit 
}.

module M(I:I): I = {
  var x:bool
  fun init():unit = {
    I.init();
    x = true;
  }
}.