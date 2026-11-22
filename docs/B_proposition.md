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
For our shallow embedding, we haven't design an *inductive type* to specify what should be allowed to construct a PM proposition, which is the common practice to set up a clear *boundary* on *what should be considered as what*. We are using Rocq's default `Prop` as the type for proposition. 

Implementation-wise, to assert a proposition `P` in Rocq, we want to design something to inhabit the type of proposition `Prop`, and it should come with the name `P`. Our shallow embedding has two ways to denote an atomic proposition `P`, a.k.a. individual:
- `Individual "p" : Prop` as our default way to claim an individual, which is an elementary proposition. If such a `P` should be asserted, it should look like `H : Individual "p"`.
- `P : Prop` as our default. If such a `P` should be asserted, it should look like `H : P`, *assuming* that `P : Prop` has been already asserted.

While they seem to be either redundant or pretty much the same, they will behave differently when we want to *substitute* them. 
- `Individual "p" : Prop` doesn't support any forms of substitution, as we haven't designed any rules on it. We have to manually specify a equation to be substituted when we need it.
- `P : Prop` usually utilizes Rocq's nature on theorems or definitions, for example the `P` in `Theorem nx_x (P : Prop)`. When we "instantiate" such a theorem `nx_x` into something with `nx_x Q`, we automatically substituting the name `P` with `Q`.

Our `Individual "p"` is specifically designed for introducing an individual in the middle of the proof, which is pretty common for forward reasoning. Such individuals will usually only to be generalized. It doesn't involve any substitution, and will not participate in the deduction of the proof, so we don't need to specify any substitutions, so `Individual "p"` turns out to be just good to use. SSReflect has a similar design to support forward reasoning, see the [have](https://coq.inria.fr/doc/V8.20.0/refman/proof-engine/ssreflect-proof-language.html#coq:tacn.have) tactic, but our design is more lightweight and ad-hoc.

We are only observing assertions within the *context window*. What will it become, if we want to observe such constructions outside of the context window? Why can we assert theorems "globally", but propositions only "locally" - and when should we make it locally? This will be a nice chance glance into Rocq's *vernac*s, and perform some little experiments. Suppose we want to assert a proposition "globally", below are some attempts:
```Rocq
(* The following definitions are supposed to be used separately *)

(* 1. Use `P` directly as the name for a proposition *)
Definition P : Prop. Admitted.
Check P.
(* P : Prop *)

(* 2. Use `Theorem` vernac rather than `Definition` *)
Theorem P : Prop. Admitted.
Check P.
(* P : Prop *)

(* 3. Use `Axiom` vernac instead *)
Axiom P : Prop.
Check P.
(* P : Prop *)

(* 4. Associate an individual to the name `P` *)
Definition P : Prop := Individual "p".
Check P.
(* P : Prop *)

(* 5. Pass in a stub `_P` to be substituted into something else when needed, while pertaining the name `P` *)
Definition P (_P : Prop) : Prop := _P.
Check P.
(* P : Prop → Prop *)

(* 6. Move the parameter `_P` from lhs of the definition to right*)
Definition P : Prop := ∀ (_P : Prop), _P.
Check P.
(* P : Prop *)
```

1. (1), (2), (3): We are observing the different usage of vernacs. `Definition` and `Theorem` are [almost the same](https://rocq-prover.org/doc/V8.20.0/refman/language/core/definitions.html); `Axiom` [only allow](https://rocq-prover.org/doc/V8.20.0/refman/language/core/assumptions.html) things to be *admitted* immediately. 
2. (1), (4): As we `Check` out, both of the examples should be the same, under the context of *proof irrevalence*: the name `P` comes with the type `Prop`, regardless of its actual inhabitent. However if we want to examine their inhabitants, (4) comes with the `Individual` we defined, while (1) is opaque and "admitted". We can also use `Print` to get a more detailed output.
3. (1), (5): Yet another way to model assertion of a proposition. This time, we are observing `Check P` producing different result(as expected). This example is inspired from how we use a *theorem*: if theorems are always "instantiated" before we use them, just like `nx_x P Q R...`, should we also design our propositions just as in such style as `P x`? We have been utilizing substitution through Rocq's functions by default, and this example questions us when & how to substitute, by proposing another option to perform it.
4. (5), (6): By moving the parameter *from left to right*, our `P` once again obtained its type `P : Prop`. Why are we getting this [difference](https://rocq-prover.org/doc/V8.20.0/refman/language/core/definitions.html), just by moving the parameter's position, and *how will this affect our design* on propositions? What is the relation between `∀ P, P` in (6), and `Prop → Prop` in (5)? Since we are starting to involve Rocq's *function* type to model our proposition, could it mess it up when we want to design *propositional function*s? Which leads to the central question above eveerything we have been discussed -

> When we are proposing a theorem with `Theorem` globally, should it be considered a *proposition* or a *function* in PM's setting?

## The propositional function
Let's think about possible options to assert a propositional function in Rocq.
1. `H1 : ∀ x, φ x` as Rocq is using `fun x => ...` as the inhabitant of `∀` type
2. `H1 : (fun x => ...)` which is impossible, unnecessary and intend to do what (1) does
3. `H1 : φ X` as claimed in [the design](./B_proposition.md/#the-design), assuming `X` has already been asserted as a proposition

Although (2) is a very absurd attempt, we will still take a closer look:
- One might expect `(fun x => ...)` can be a type. It turns out that this is only designed to be an inhabitant for `∀`, and never the other way around
- By CH correspondance, `→` is used as the type for a function
- By Rocq's design, `→` is a special case for `∀`, which will be explained below; thus `(fun x => ...)` could also be an legal inhabitant of `→`
...Where none of these connections has been assumed in PM, and we can very easily mess all them up in the shallow embedding.

It turns out that `∀` is such fundamental that it is the *dependent product type* itself, according to Rocq's [type system's design](https://rocq-prover.org/doc/V8.20.0/refman/language/cic.html). `P → Q` is inherently viewed as `∀ _ : P, Q`. One might wonder if we can design PM's function type without involving `∀`, which is almost impossible. To assert a function, or to design a proper type to represent the functions, we might design something like
```Rocq
Definition Fun (parameters : ...) := ∀ parameters, ...
```

...Which seems to be pretty close to the option (1). 

With situations concerned in the [proposition](./B_proposition.md/#the-proposition), we are adding chaos over chaos. What else should turn out to be a `∀` in Rocq, globally?...

TODO: redesign examples
``` Rocq
Definition example_1 (P : Prop) : P → P.
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

(* ...even in the goal window *)
Goal True.
  (* Try to change `pose` into `pose proof` by yourself *)
  pose proof example_1 as H1.
  pose proof example_2 as H2.
  pose proof example_3 as H3.
  pose proof example_4 as H4.
Admitted.
```
TODO: example should concern about:
- add extra numbers continue from proposition examples
- parameters on lhs/rhs
- apparent variables and real variables
- Theorems that whenever we use, we are required to instantiate all of its parameters
- appearing in context window vs appearing globally

TODO: for a forall, we might inherently
- already specified which `forall` should be already used beforehead
- view which part as the actual part constitute to the object we are defining
- more specifically, might be the difference between apparent variables or real variables


TODO:
- Placing a variable in *lhs* or *rhs* has actually been a mixture of several situations in our shallow embedding:
- 1. We might present PM's *apparent variables* on the `rhs`, marking them `∀`-typed correctly
- - Some `→` are propositional implications, while others are functions
- - Some `∀` are real variables, while others are apparent variables; everything will be collapsed
- - Even if we want to design without `∀`, Rocq's nature makes we cannot just type them(easy to be solved)...
- - In context window, everything in lhs will collapse to rhs cases
- 2. We might also present a variable to have it asserted at *lhs* like `∀ (P : Prop)`. This variable will come with a Rocq's `∀` type, but as a PM's *real variable* it is not supposed to be quantified
- 3. Our function type is Rocq's default `Prop → Prop` involving `→` type, ...as we are using `→` type as the default for function type such as `Prop → Prop`, on lhs: function's type; on rhs: conflict with `P → P`
- 4. When we have a parameter on the lhs with `→`(function), TODO...
- 5. We might use the `→` as the function type like `Prop → Prop` on the *rhs*(??), potentially introduce a function as its inhabitant(TODO: recheck this)


- Theorems always with parameters instantiated: looks like a proposition, but actually a function since we have the substitution?

TODO: Summary
  - our current design of soft embedding is inherently using \*1.11 by the analysis above; to make it clearer, for \*1.1 we should have (TODO: to explore with example snippets)
  - Our project doesn't design a proper function type, but should be a feature in the future
  - we are pretty close to assuming propositional functions in such sense
  - state that for historical reasons we haven't think of how to model functions properly
  - for shallow embedding, we don't have formal semantics, but we instead discuss on how *deep* can we integrate with Rocq's existing features, as fit as possible

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