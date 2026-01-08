# Mechanics of Principia Mathematica

TODO: organize the mechanics in a chapter-splitted style

## Chapter organization
Principia Mathematica seems to define its concepts in an **incremental way**. That means:
1. Some early chapters define some rough ideas and develop theorems on them
2. Later chapters might refine some of these ideas and define different cases for the ideas. If previous chapter only considers animals, later chapters might divide animals into dogs and cats
3. Correspondingly, theorems in previous chapters will be given new meanings in later chapters. This might suggest we use typeclasses and instances to "register" new meanings for later chapters if we want to correctly formalize Principia.

We now proceed to explain how every math elements are being built, bottom-up, in Principia.

## The system
For every theorem, we have two ways to use it. One is we refer to it just like a "function", and another one is prove the theorem by inference.

When we *refer* to the theorems, we are allowed to substitute every single literals with some new propositions, just like what you see in theorem provers.

When we want to prove them, we start with a set of individuals like `P`, `Q`, `R`. They are not propositions(as stated in Principia), cannot be further splitted and substituted. **New individuals that are not presented in the theorems though, is allowed to be introduced** - in the middle of proving, we might occur to a new individual like `S`.

(TODO: are individuals able to be changed in any time? )

Elementary propositions are simple propositions connected with `~` and `\/`.

TODO: polish as below
1. Fundamentally we have a set of individuals like `P`, `Q`, `R`. They are not propositions, and they cannot be further splited.
2. Elementary propositions are simple propositions connected with `~` and `\/`. (Put it in another way, these `~` and `\/`s are defined on elementary propositions)
3. `x^`, a function, is defined on an *already defined proposition* by abstracting all occurrences of `x` in the proposition. (Principia seems to be hasn't considered about the bound variables and free variables?) For example. if we have `x /\ y`, then `(x /\ y)x^` is a function that should be written now as `fun x => x /\ y`.
4. `Phi x` means the result of the application, of a function `Phi x^` onto a parameter `x`. Our function contains only 1 variable and ranges over elementary propositions.
5. `forall` and `exists` are defined by directly and only quantifying over a function.

how PM is different from modern type theories:
1. types are for propositions
2. individuals are not types
3. individuals can be substituted with more complex terms by infinite times(?TODO: check if there is some severe bug in formalization)

TODO: extend to descriptions and classes in the future; slightly compare to type systems

TODO: the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of ~ and \/