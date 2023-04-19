(*TODO: Pierre-Yves*)
abstract theory Foo.
  abstract theory Bar.
    abstract theory FooBar.
      type t.
    end FooBar.
  end Bar.
end Foo.

clone import Foo as FooFoo
  rename [theory] "Bar" as "Foo".

(*rename should have an option to only target the theory Bar,
  and not all theories with Bar in the name, such as FooBar.*)
print FooFoo.
