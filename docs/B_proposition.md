# Appendix B: Propositions, functions, individuals and matrices

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

----------
**Update 2026.11.17:** This [φlOverflow Q&A][PO] has been our primary source, having a massive impact on rewriting most of the documentation. 

## Propositional functions
Recall what we have described in chapter 1 in [mechanics](./3_mechanics.md/#chapter-1):
- Having something in context window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style.
- `H1 : (∀ x, φ x)` is expected to mean asserting an **elementary propositional function**. 
- (\*1.11)If `H2 : (∀ x, φ x → ψ x)` can be implied, then we are allowed to imply `H3 : (∀ x, ψ x)`.
- Being the actual *modus ponens*, \*1.11 is said to be used almost everywhere, and \*1.1 is generally not used(p.93). 

For Principia's design, propositions and functions should be "practically the same"(p.18). In Rocq, we prove `P` is true if `P` has an inhabitant; `H1 : P` means `P` as a type being presented, has an inhabitant `H1`. To really understand what should be the difference between propositions and propositional functions if we implement with Rocq's default, we will demonstrate the relation with examples.
```Rocq
Definition example_proposition : Prop. Admitted.

Definition example_function (P : Prop) : Prop := P → P.
Print example_function.
(* = fun P : Prop => P → P : Prop → Prop *)

Theorem example_theorem (P : Prop) : P → P. Admitted.
Check example_theorem.
(* ∀ P : Prop, P → P *)

(* Let check what will happen during proving... *)
Goal ∀ (P : Prop), True.
  intro P.
  pose (example_theorem P) as H1.

  (* Notice how both of below are the same... *)
  pose (example_function) as H2. unfold example_function in H2.
  pose (fun (P : Prop) => P → P) as φ.
  (* fold (H2 P) in H1. *)
  fold (φ P) in H1.
Admitted.
```

With examples above,
- We can abstract that proposition that the `example_theorem` inhabits into a function applying to a variable
- Rocq's function has tactics like `fold` to perform such abstraction, but we didn't expand such move in shallow embedding. We mostly don't state the function explicitly, and instead `rewrite` a function on the fly
- To the very center of our questions: when we are asserting a theorem, should it be a function or a proposition by PM's definition?

In particular, observe the type of *example_theorem*, which can be abstracted as `∀ P : Prop, φ P`, the `∀ P : Prop` allows us to take in a `P` for substitution, so that `φ P` can produce different propositions, while it is also a valid type for a theorem. So it has been concluded for now that `∀ P : Prop, φ P` should be the adequate type for asserting a function in Rocq.

In Rocq, a theorem is being made by providing an inhabitant to a *proposition* or a *function*, but when using a theorem, we always require the theorem to be "instantiated". These parameters like `P : Prop` are used to conviniently perform substitutions, for which we shouldn't have for a proposition, by the definition of PM. We therefore have the following **assumptions** being made:

> **Assumption 1**. Within chapter 1 - 5, all Rocq `Theorems`s are inherently asserting as PM's propositional functions
>
> **Assumption 2**. Within chapter 1 - 5, tactic `MP` for *modus ponens* should always inherently refer to \*1.11, and never \*1.1

## Matrices and individuals
For shallow embedding, we haven't designed an *inductive type* to specify what should be allowed to construct a PM proposition, which is the common practice to set up a clear *boundary* on *what should be considered as what*. We are using Rocq's default `Prop` as the type for proposition, but it allowed too much "propositions" than we want. For example, theorems usually introduces parameters with `∀`, but such `∀`s are not supposed to be counted as PM's `∀`s.

For a individual `P`, a.k.a. an atomic proposition, we should have two ways to denote it:
- `Individual "p" : Prop` as the default way to claim an individual, which is an elementary proposition. If such a `P` should be asserted, it should look like `H : Individual "p"`.
- `P : Prop`. If such a `P` should be asserted, it should look like `H : P`, *assuming* that `P : Prop` has been already asserted.

While they seem to be either redundant or pretty much the same, they behave differently when we want to *substitute* them. 
- `Individual "p" : Prop` doesn't support any forms of substitution, as we haven't designed any rules on it. We have to manually specify a equation to be substituted when we need it.
- `P : Prop` usually utilizes Rocq's nature on theorems or definitions, for example the `P` in `Theorem nx_x (P : Prop)`. When we "instantiate" such a theorem `nx_x` into something with `nx_x Q`, we automatically substituting the name `P` with `Q`.

`Individual "p"` is specifically designed for introducing an individual in the middle of the proof, which is pretty common for forward reasoning. Such individuals will usually only to be generalized. It doesn't involve any substitution, and will not participate in the deduction of the proof, so we don't need to specify any substitutions, so `Individual "p"` turns out to be just good to use. SSReflect has a similar design to support forward reasoning, see the [have](https://coq.inria.fr/doc/V8.20.0/refman/proof-engine/ssreflect-proof-language.html#coq:tacn.have) tactic, but our design is more lightweight and ad-hoc.

Next, we come to matrices, with reference to [φlOverflow Q&A][PO]. We still recall how matrix is stated within the original text:
1. (p.162)Matrix is a function with arbitrary length of variables, but without any apparent variables("For the sake of clearness...")
2. (p.164)PM's hierarchy comes to design so that *variables in the hierarchies are either individuals or matrices*("A function is said to be predicative when it is a matrix..."). Which means
    1. Matrices can be applied, or apply onto matrices, just like functions
    2. At the same time, matrices can be asserted, just like propositions
    3. On the other hand, the definition of propositions has become narrower to "propositions" with all variables quantified
3. (p.164)"Propositions, which have occurred hitherto as variables, will no longer do so except in a few isolated cases of which no subsequent use is made."

This time, we demonstrate the difference against propositional function, by referring to the pseudo code in [φloverFlow Q&A][PO].
```Rocq
(* For propositional functions *)
f (Individual "p")                       (* allowed *)
f (λ p q. p ∨ q)                         (* not allowed *)
f ((Individual "p") ∨ (Individual "q"))  (* allowed *)

(* For matrices *)
f (Individual "p")                       (* allowed *)
f (λ p q. p ∨ q)                         (* allowed, as variable can be a matrix *)
f ((Individual "p") ∨ (Individual "q"))  (* not allowed! *)
```

As we are modeling PM's propositional functions with lambda calculus, we need to state its important difference against lambda calculus: we don't need a parameter list, because it is useless. To be more exact:
- Although variables for a PM's function will be all letters occurred in their proposition, they are either
  - totally unordered, or
  - take the default occurrence from left to right as its order, which is still lacking of specification
- PM's function is always small-step and manually specified how to compute

Based on original text in PM, and analysis above on how matrix should behave, we conclude the following rules to model a matrix:
- Matrix can be modeled just like a function, presented as a lambda closure; but with different computation rule
- The computation rule for matrix `f1 := (fun x => P x)` and `f2 := (fun y => Q y)` should be `f1 f2 := (fun y => P (Q y))`
- For cases with multiple parameters, they are beyond specification

It shall be derived that, Rocq's function is enough to model PM's matrix, but it cannot be applied as expected, as we haven't design a computation rule for matrix so far. We have the following assumption:

> **Assumption 3**. After chapter 12, all Rocq `Theorems`s are inherently asserting as PM's matrices

## Summary
As we are designing a shallow embedding, we don't model PM by presenting a formal semantic, but instead discuss how *deep* can we integrate PM into Rocq's existing features, as fit as possible.

Even though we have made it clear that how should the shallow embedding correspond to PM's specification, this article has been written long after we have completed most of the code, leaving the design of embedding potentially outdated. Furthermore, 
- Although with *Assumption 1* being made, by `example_function` and `example_theorem`, we can see that theorems are not having the type of functions; they only inhabit a proposition, to hint the existence of a trait of functions
- We have not considered anything on how to type the *order* of a theorem or a proposition, or even how to type a function under the full proposition hierarchy
- `Prop` has been too big for functions to admit a parameter, or for propositions to be typed

[PO]: https://φlosophy.stackexchange.com/questions/139085/exact-definition-for-elementary-proposition-and-function-in-principia-mathematic/139086#139086