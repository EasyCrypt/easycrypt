module type I = { 
  proc f() : unit
  proc init () : unit 
}.

module type IF (X:I) = { 
  proc init() : unit { X.init }
}.

module F(X:I) : IF(X) = { 
   proc f() : unit = { X.f(); }
   proc init() : unit = { X.init();}
}.
