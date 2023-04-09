(*TODO: Pierre-Yves*)

abstract theory Foo.
  lemma l : true by trivial.
end Foo.

abstract theory Bar.
  clone import Foo.
end Bar.

abstract theory FooBar.
  clone import Bar.
  (*We should be able to clear recursively Bar and all it's sub theories,
    with something like clear [Bar.**].*)
  clear [Bar.* (* Bar.Foo.* *)].
end FooBar.

print FooBar.
