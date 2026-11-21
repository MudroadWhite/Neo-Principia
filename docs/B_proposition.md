# Appendix B: Propositions, functions, individuals and matrices

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

----------
**Update 2026.11.17:** This [PhilOverflow Q&A][PO] has been our primary source, having a massive impact on rewriting most of the documentation. 

## The design
Recall what we have described in chapter 1 in [mechanics](./3_mechanics.md/#chapter-1):
> - Having something in our context window means it has been asserted/implied true
> - Asserting `H1 : P` means asserting `P` as an **elementary proposition**
> - (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) → (|- Q)`(p.92), which doesn't occur within formulae in PM.
> - If proposition `X` has been already asserted, `H1 : φ X` is expected to mean asserting an **elementary propositional function**. 
> - (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.

In Rocq, we prove `P` is true if `P` has an inhabitant; `H1 : P` means `P` as a type being presented, has an inhabitant `H1`. Observe that `H1 : P` and `H1 : φ X` are essentially the same thing, unless `P` is an individual. For Principia's design, they should be "practically the same"(p.18). 

## The proposition
For our shallow embedding, we haven't design an *inductive type* to specify what should be allowed to construct a PM proposition, which is the common practice to set up a clear *boundary* on *what should be considered as what*. We are using Rocq's default `Prop` as the type for proposition; implementation-wise, our shallow embedding has two ways to denote an atomic proposition `P`, a.k.a. individual:
- `Individual "p" : Prop` as our default way to claim an individual, which is an elementary proposition. If such a `P` should be asserted, it should look like `H : Individual "p"`.
- `P : Prop` as our default. If such a `P` should be asserted, it should look like `H : P`, *assuming* that `P : Prop` has been already asserted.

While they seem to be either redundant or pretty much the same, they will behave differently when we want to substitute them. 
- `Individual "p" : Prop` doesn't support any kinds of substitution, as we haven't designed any rules on it. We have to manually specify a equation to be substituted when we need it.
- `P : Prop` usually utilizes Rocq's nature on theorems or definitions, for example the `P` in `Theorem nx_x (P : Prop)`. When we "instantiate" such a theorem `nx_x` into something with `nx_x Q`, we are automatically substituting prposition `P` with `Q`.

Our `Individual "p"` is specifically designed for introducing an individual in the middle of the proof, which is pretty common for forward reasoning. Such individuals will usually only to be generalized. It doesn't involve any substitution, and will not participate in the deduction of the proof, so we don't need to specify any substitutions, so `Individual "p"` turns out to be just good to use. SSReflect has a similar design to support forward reasoning, see [**TODO: ask AI for ssreflect reference**](), but our design is more lightweight and ad-hoc.

Suppose we want to define such a proposition to be used, rather than just observing them from the conext window when we want to prove a goal. We might have following ways to make such a definition:
```Rocq
(* Using `P` directly as the name for a proposition *)
Definition P : Prop. Admitted.

(* Associating an individual to the name `P` *)
Definition P : Prop := Individual "p".

(* Pass in a stub `_P` to pertain the name `P`, also allow `P` to be substituted into something else when needed *)
Definition P (_P : Prop) : Prop := _P.
```

Such options have revealed us another question: which should be the correct choice to assert a proposition `P`?

## The function
Let's check back how should we assert a propositional function in Rocq. We should have the following options to represent the assertion:
1. `H1 : ∀ x, φ x` as Rocq is using `fun x => ...` as the inhabitant of `∀` type
2. `H1 : (fun x => ...)` which is impossible, unnecessary and intend to do what (1) does
3. `H1 : φ X` as claimed in [**TODO: The design**](), assuming `X` has already been asserted as a proposition

Although (2) is a very naive attempt, we can still give a closer look. The same should apply to a function, except that 
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

As above shows, we have attemped to use different *vernac*s to present the same proposition, and it turns out that
- To present a theorem, vernac `Theorem` can do pretty much what `Definition`does(example_1 & example_2, and [official reference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/definitions.html))
- To present an axiom to be admitted by default, `Theorem` and `Axiom` are different with each others. (example_3, example_4 & example_5, and [official reference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/assumptions.html))

Despite `example_2` and `example_3` being the same, we present them with different manners: `example` comes with a parameter `P` on the left hand side of the `:=`, and `example_3` moves the `P` to the right with a `∀`. Yet again, [official reference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/definitions.html) can be a primary souce to see why this happens. 

TODO:


We want to view `P -> P` as a proposition, or `forall P, P -> P` as a proposition, or `forallP, P -> P` as a function?
What are the default part that we should be introduced into context?


Placing a variable in *lhs* or *rhs* has actually been a mixture of several situations in our shallow embedding:
1. We might present PM's *apparent variables* on the `rhs`, marking them `∀`-typed correctly
- Some `->` are propositional implication, while others are functions
- Some `forall` are real variables, while others are apparent variables; everything will be collapsed
- Even if we want to design without `forall`, Rocq's nature makes we cannot just type them(easy to be solved)...
- How should we type a function?
- In context window, everything in lhs will collapse to rhs cases
- lhs: what are the options
- how can we decide if we are actually using 1.11 or 1.1?

2. We might also present a variable to have it asserted at *lhs* like `∀ (P : Prop)`. This variable will come with a Rocq's `∀` type, but as a PM's *real variable* it is not supposed to be quantified
3. Our function type is Rocq's default `Prop -> Prop` involving `->` type, ...

as we are using `→` type as the default for function type such as `Prop -> Prop`, on lhs: function's type; on rhs: conflict with `P -> P`

4. When we have a parameter on the lhs with `→`(function), TODO...
3. We might use the `→` as the function type like `Prop → Prop` on the *rhs*(??), potentially introduce a function as its inhabitant(TODO: recheck this)

TODO: state that for historical reasons we haven't think of how to model functions properly


TODO: Summary
  - our current design of soft embedding is inherently using \*1.11 by the analysis above; to make it clearer, for \*1.1 we should have (TODO: to explore with example snippets)
  - Our project doesn't design a proper function type, but should be a feature in the future
  - we are pretty close to assuming propositional functions in such sense

TODO: 
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
- collect related discussions on lhs & rhs in the chapters, and through all the documentations
- collect related discussions on `Theorem` and `Definition` through all the documentations
- collect related discussions on ambiguities through all the documentations, and said we have solved the ambiguity after a long time