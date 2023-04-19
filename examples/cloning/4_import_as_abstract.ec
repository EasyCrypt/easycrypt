(*TODO: Pierre-Yves*)

abstract theory Foo.
  type t.
end Foo.

clone import Foo as Bar.

(*There should be an option to import Foo as an abstact theory, the
  expected end result being that Bar is abstract.*)
print Foo.
print Bar.
