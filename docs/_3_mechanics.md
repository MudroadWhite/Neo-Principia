# Mechanics of Principia Mathematica

We are building: 
- [x] Chapter 9 - A demonstration set of theorems to show chapter 1 - 5 can be extended to quantified propositions(with single "apparent variable"). Basic support for a predicate called "IsSameType". Support for instantiating individuals.
- [x] Chapter 10 - The real and practical alternative to chapter 9, being used in later chapters. Material implications converted to formal implications. Notation supports for `→` and `↔` with single apparent variable. One theorem seems to be unprovable.
- [x] Chapter 11 - Quantified propositions extended to more than one variables. Similarly, extended notation supports for `→` and `↔`.
- [x] Chapter 12 - Axiom of reducibility, and its conceptual support, the `Predicate` predicate.
- [x] Chapter 13 - Propositional equality(different from definitional equality). Support for instantiating predicative functions. One theorem seems to be unprovable.
- [ ] \[WIP\]Chapter 14 - The `iota` operator for descriptions, a predicate `iota_E` for its *existence* statement. Theorems on them.

## What is Principia Mathematica?
From wiki's entry of [History of type theory](https://en.wikipedia.org/wiki/History_of_type_theory), the "type system" we are formalizing is called "ramified theory of types". 

Commonly used type systems(or just the default of Rocq) get us "common sense": propositions are elements of sets, functions are modeled with lambda calculus, etc.. the most significant one: by the noted CH correspondence, everything are either types or elements under types. These "common sense" fail in ramified theory of types: Propositions are not types. Sometimes for brevity they are untyped. The inference is performed by rewriting on propositions. Types in this system play on a much more auxiliary role, and ramified theory of types, is actually a rewriting system.

We now proceed to explain how every math elements are being built, bottom-up, in Principia.

## How does Principia define everything?
Different from most of the textbooks, Principia defines its concepts in a **compositional way**. In contrast to *`~ a` should be defined as something*, chapter 9 demonstrates, immediately, things like *`~` applied on an `∃` proposition should be defined as something*. It's a common practice to fix an operator and assign a function for its interpretation, but Principia usually involves 2 operators at a time. 

Principia also defines in an **incremental way**. That means:
1. Some early chapters define rough ideas and propose their theorems. For example, we define what is an *animal*, and write down theorems about it.
2. Later chapters might refine the rough idea and split for different cases. We divide *animal*s into *dog*s and *cat*s.
3. Theorems on *animal*s will be given new meanings immediately.

Principia also defines its theorems in a **"practical way"**. Theorems in chapter 10 are being proposed, because they are useful in later chapters, not because they address important properties for first order logic, not to mention soundness and completeness.

## How does Principia rewrite everything?
TODO: 

For every theorem, we have two ways to use it. One is we refer to it just like a "function", and another one is prove the theorem by inference.

When we *refer* to the theorems, we are allowed to substitute every single literals with some new propositions, just like what you see in theorem provers.

When we want to prove them, we start with a set of individuals like `P`, `Q`, `R`. They are not propositions(as stated in Principia), cannot be further splitted and substituted. **New individuals that are not presented in the theorems though, is allowed to be introduced** - in the middle of proving, we might occur to a new individual like `S`.

(TODO: are individuals able to be changed in any time? )
(TODO: refer to `architecture` chapter, and maybe update the corresponded part)

how PM is different from modern type theories:
1. individuals are not propositions(???)
2. individuals can be substituted with more complex terms by infinite times(?TODO: check if there is some severe bug in formalization)

TODO: the mechanics of registration: if we have proven something is safe to use, we're supposed to extend the original symbols to new field, e.g. definition of ¬ and ∨

## The system

TODO: organize the mechanics in a chapter-splitted style

Elementary propositions are simple propositions connected with `¬` and `∨`.

TODO: polish as below
1. Fundamentally we have a set of individuals like `P`, `Q`, `R`. They are not propositions, and they cannot be further splited.
2. Elementary propositions are simple propositions connected with `¬` and `∨`. (Put it in another way, these `¬` and `∨`s are defined on elementary propositions)
3. `x^`, a function, is defined on an *already defined proposition* by abstracting all occurrences of `x` in the proposition. (Principia seems to be hasn't considered about the bound variables and free variables?) For example. if we have `x ∧ y`, then `(x ∧ y)x^` is a function that should be written now as `fun x => x ∧ y`.
4. `Phi x` means the result of the application, of a function `Phi x^` onto a parameter `x`. Our function contains only 1 variable and ranges over elementary propositions.
5. `∀` and `∃` are defined by directly and only quantifying over a function.
6. descriptions...
