# Mechanics of Principia Mathematica

1. Fundamentally we have a set of individuals like `P`, `Q`, `R`. They are not propositions, and they cannot be further splited.
2. Elementary propositions are simple propositions connected with `~` and `\/`. (Put it in another way, these `~` and `\/`s are defined on elementary propositions)
3. `x^`, a function, is defined on an *already defined proposition* by abstracting all occurrences of `x` in the proposition. (Principia seems to be hasn't considered about the bound variables and free variables?) For example. if we have `x /\ y`, then `(x /\ y)x^` is a function that should be written now as `fun x => x /\ y`.
4. `Phi x` means the result of the application, of a function `Phi x^` onto a parameter `x`. Our function contains only 1 variable and ranges over elementary propositions.
5. `forall` and `exists` are defined by directly and only quantifying over a function.

TODO: extend to descriptions and classes in the future; slightly compare to type systems

TODO: the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of ~ and \/