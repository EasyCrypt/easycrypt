(* ==================================================================== *)
subtype 'a word (n : int) = {
  w : 'a list | size w = n
} + witness.

op cat ['a] [n m : int] (x : {'a word n}) (y : {'a word m}) : {'a word (n+m)} =
  x ++ y.

==> (traduction)

op cat ['a] (x : 'a word) (y : 'a word) : 'a word =
  x ++ y.

lemma cat_spec ['a] :
  forall (n m : int) (x y : 'a word),
    size x = n => size y = m => size (cat x y) = (n + m).

op xor [n m : int] (w1 : {word n}) (w2 : {word m}) : {word (min (n, m))} =
  ...

lemma foo ['a] [n : int] (w1 w2 : {'a word n}) :
  xor w1 w2 = xor w2 w1.

op vectorize ['a] [n m : int] (w : {'a word (n * m)}) : {{'a word n} word m}.

-> Keeping information in application? Yes
   -> should provide a syntax for giving the arguments

      {w : word 256}

      vectorize<:int, n = 4> w ==> infer: m = 64

-> What to do when the inference fails
   1. we reject (most likely)
   2. we open a goal

-> In a proof script (apply: foo) or (rewrite foo)
   1. inference des dépendances (n, m, ...)
   2. décharger les conditions de bord (size w1 = n, size w2 = n)

-> Goal
      n : int
      m : int
     w1 : {word n}
     w2 : {word m}
   ====================================================================
     E[xor (cat w1 w2) (cat w2 w1)]

   rewrite foo

      n : int
      m : int
     w1 : {word n}
     w2 : {word m}
   ====================================================================
     E[xor (cat w2 w1) (cat w1 w2)]

   under condition:
     exists p . size (cat w1 w2) = p /\ size (cat w2 w1) = p.

   ?p = size (cat w1 w2)
   ?p = size (cat w2 w1)

-> can be solved using a extended prolog-like engine
    1. declarations of variables (w1 : {word n}) (w2 : {word m})
    2. prolog-like facts from operators types (-> ELPI)
    3. theories (ring / int)

-> subtypes in procedures

   We can only depend on operators / constants. I.e. the following
   program should be rejected:

   module M = {
     var n : int

     proc f(x : {bool word M.n}) = {
     }
   }

   Question:
     - What about dependent types in the type for results:
         we reject programs if we cannot statically check the condition
     - What about the logics? we have to patch them.

(* ==================================================================== *)
nth ['a] 'a -> 'a list -> int -> 'a

ws : {word n} list

nth<:word> witness ws 2 : word
nth<:{word n}>

coercion : 'a word n -> 'a list
