# Appendix B: Propositions, functions, individuals and matrices

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

----------
**Update 2026.11.17:** This [PhilOverflow Q&A][PO] has been our primary source, having a massive impact on rewriting most of the documentation. 

Recall what we have described in chapter 1 in [mechanics](./3_mechanics.md/#chapter-1):
> - Having something in our proof window means it has been asserted/implied true
> - Asserting `H1 : P` means asserting `P` as an **elementary proposition**
> - (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) → (|- Q)`(p.92), which doesn't occur within formulae in PM.
> - If proposition `X` has been already asserted, `H1 : φ X` is expected to mean asserting an **elementary propositional function**. 
> - (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.

Observe that `H1 : P` and `H1 : φ X` are essentially the same thing, unless `P` is an individual. For Principia's design, they should be "practically the same"(p.18). But let's check how should these type be understood in Rocq's default. We have the following options to represent the assertion of a function:
1. `H1 : ∀ x, φ x` as Rocq is using `fun x => ...` as the inhabitant of `∀` type
2. `H1 : (fun x => ...)` which is impossible, unnecessary and intend to do what (1) does
3. `H1 : φ X` as in this project, assuming `X` has already been asserted as a proposition

Although (2) is a very naive attempt, we can still give a closer look. In Rocq, we prove `P` is true if `P` has an inhabitant; `H1 : P` means `P` as a type being presented, has an inhabitant `H1`. The same should apply to a function, except that 
- `(fun x => ...)` is designed to be an inhabitant for `∀`, and never a type on its own
- `→` is a special case for `∀`, thus `(fun x => ...)` could also be an legal inhabitant of `→`
- By CH correspondence, `→` is also used as the type for a function
Where none of these connections has been assumed in PM, and we can very easily mess all them up.

To assert a function, we need to design a proper type to represent the functions and get it *inhabited*, as something like `Func X (expression...)`... which seems to be pretty close to our option (1). One might wonder if we can design another type similar to `∀` without involving `∀` itself for confusions. `∀` turns out to be such a fundamental type that it is directly the *dependent product type*, according to Rocq's [type system's design](https://rocq-prover.org/doc/V8.20.0/refman/language/cic.html). That being said, if we want to define a type for function, it can only look like:

```Rocq
Definition Fun (parameters : ...) := ∀ parameters, ...
```

We move on to discover what else would turn out to be a `∀` in Rocq. Consider the following examples:
``` Rocq
Definition example_1 (P : Prop) : P → P.
Proof. auto. Qed.

(* The `Theorem` vernac is pretty much the same as `Definition` *)
Theorem example_2 (P : Prop) : P → P.
Proof. auto. Qed.

Theorem example_3 : ∀ (P : Prop), P → P.
Proof. auto. Qed.

(* `Axiom` vernac doesn't need a proof *)
Axiom example_4 : ∀ (P : Prop), P → P.

(* On the other hand, it doesn't allow the following: *)
(* Axiom example_5 (P : Prop) : P. *)

(* We can see that all examples above should be the same thing... *)
Check example_1.
(* ∀ P : Prop, P → P *)
Check example_2.
(* ∀ P : Prop, P → P *)
Check example_3.
(* ∀ P : Prop, P → P *)
Check example_4.
(* ∀ P : Prop, P → P *)

(* ...even in the proof window *)
Goal True.
  (* Try to change `pose` into `pose proof` by yourself *)
  pose proof example_1 as H1.
  pose proof example_2 as H2.
  pose proof example_3 as H3.
  pose proof example_4 as H4.
Admitted.
```

As above shows, we have attemped to use different *vernacs* to present the same proposition, and it turns out that
- To present a theorem, vernac `Theorem` can do pretty much what `Definition`does(example_1 & example_2, and [official reference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/definitions.html))
- To present an axiom to be admitted by default, `Theorem` and `Axiom` are different with each others. (example_3, example_4 & example_5, and [official reference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/assumptions.html))

Also, observe that `example_2` and `example_3` are also the same, but we present them with different manners: `example` comes with a parameter `P` on the left hand side of the `:=`, and `example_3` moves the `P` to the right with a `∀`. **TODO**: We have the following conclusions: 
- parameters in rhs are arrow-typed by default, being regarded as apparent variables
- parameters in lhs are ∀-typed in disguise, being regarded as real variables


TODO: Summary
  - our current design of soft embedding is inherently using \*1.11 by the analysis above; to make it clearer, for \*1.1 we should have (TODO: to explore with example snippets)
  - Our project doesn't design a proper function type, but should be a feature in the future
  - we are pretty close to assuming propositional functions in such sense

TODO: 
- Individuals: 
  - for PM, can be introduced during the middle of the proof
  - such individuals will usually only to be generalized, and will not participate in the deduction of the proof
  - has to be separately asserted if we need to assume `Individual "p" = P`, but should never occur and good to use
  - possible reference: ssreflect for forward reasoning style? **TODO**: slightly do some research
- Matrices
  - give example from [PhilOverflow Q&A][PO]
  - explain how matrix is designed
    1. (p.162)Matrix is a function with arbitrary length of variables, but without any apparent variables("For the sake of clearness...")
    2. (p.164)PM's hierarchy comes to design so that *variables in the hierarchies are either individuals or matrices*("A function is said to be predicative when it is a matrix..."). Which means
        1. Matrices can be applied, or apply onto matrices, just like functions
        2. At the same time, matrices can be asserted, just like propositions
        3. On the other hand, the definition of propositions has become narrower to "propositions" with all variables quantified
    3. (p.164)"Propositions, which have occurred hitherto as variables, will no longer do so except in a few isolated cases of which no subsequent use is made."
  - explain difference from functions

```Rocq
TODO: 
Suppose we have a function `f1 := (fun x y => x /\ y)` and another function `f2 := (fun p q → p \/ q)`, and we want to substitute the `x` in `f1` with `p \/ q`. By Russell's idea, we shall be allowed to construct the application form as `f1 f2` and the result of the application should be `f1 f2 = (fun p q y => (p \/ q) /\ y)`. We can immediately see that lambda calculus seems like a tedious design for such abstraction; and Russell designs the representation for functions just exactly like propositions. The result shall be `(X /\ Y) (P \/ Q) = ((P \/ Q) /\ Y)` if we are clear that `X` is to substituted by `f2`.

```


[PO]: https://philosophy.stackexchange.com/questions/139085/exact-definition-for-elementary-proposition-and-function-in-principia-mathematic/139086#139086

**TODO**: 
- collect related discussions about lhs & rhs in the chapters, and through all the documentations
- collect related discussions about `Theorem` and `Definition` through all the documentations
