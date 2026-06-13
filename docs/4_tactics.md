# Tactics
> The story starts with a very simple beginning. It just isn't always working.

As mentioned in previous chapters, we "just `pose` and `rewrite`". This chapter is going to expand the slogan in complete details.

| PM Feature                                                      | Implementation                                  |
|-----------------------------------------------------------------|-------------------------------------------------|
| **Part 1: Meta theory**                                         | -                                               |
| Pp and Df                                                       | Monomorphic Rocq `Definition`                   |
| Thm                                                             | Monomorphic Rocq `Theorem`                      |
| Real & Apparent variables                                       | lhs and rhs of a Rocq theorem                   |
| Functions                                                       | Rocq lambda calculus                            |
| General `∀`, `∃`, `↔` and other logical connectives             | Rocq's equivalent default                       |
| Modus Ponens, Syllogism, etc.                                   | `MP`, `Syll`, other self defined tactics        |
| `Hp`                                                            | Rocq `intro`                                    |
| Incomplete symbols with scopes                                  | Polymorphic `Notation`s with lambda calculus    |
| Predicativity/impredicativity                                   | `!` without actual implementation               |
| Proposition order                                               | `Order` type                                    |
| Theorem polymorphism                                            | The Variant mechanic                            |
| Extra instances/interpretations                                 | The `Intro` mechanic                            |
| Symbol interpretation                                           | `let` clause + `class_func_associate`           |
| **Part 2: Computation**                                         | -                                               |
| Stepping forward                                                | `assert`                                        |
| Conclude a step/a proof                                         | `apply`+`now`/`exact`                           |
| Asserting a proposition                                         | `pose proof` only                               |
| Rewriting on a proposition                                      | "PM-based" tactics or `rewrite`/`setoid_rewrite`|
| `=` rewriting                                                   | `eq_to_equiv`+`setoid_rewrite`                  |

**Table 4.1: Full PM features considered and their implementations in Rocq**

## How do we assert a statement is true?
**Just `pose` it.** To assert a cited theorem is true, we `pose` a proof, which is pretty elementary in Rocq. Voila.

To actually pose a theorem, we have still made a tradeoff. `pose` can ensure the proof window logically correct, but *visually* awful. Proof terms will take away a large part of space, before the type of terms come into our view. We are not doing backward reasoning, nor are these proof terms meaningful - we will use a lot of `setoid_rewrite`, being introduced in later section. `pose proof` becomes our final choice.

`pose proof` doesn't solve a goal. `apply` allows us to solve the goal automatically with a theorem. `now` allows us to solve the goal as soon as we have deduced the right proposition. `exact`, as mentioned in the [architecture](./2_architecture.md), is exclusively used to hint that we have covered all steps in a proof to conclude a `Qed`.

**For extra variables, we use the `Intro` mechanic.** See for example \*9.37, adding a new real variable in the middle of the proof, just to be *generalized* in the future. To resolve this, we add a series of axioms in `lib.v`, prefixed with `Intro_`, and add a line of `set (X := Intro_ ...)` in the `TOOLS` section. This is called the `Intro` mechanic. Without the `Intro` mechanic, intermediate statements cannot be normally asserted.

## How do we rewrite a proposition?
To answer this question, we have to identify how many different ways are there in PM to rewrite. We recall the summarization in [mechanics](./3_mechanics.md/#chapter-9):
- Modus ponens, which starts from \*1.11, but generalize manually to more cases once a new notion/symbol has been introduced into a chapter
- Generalization, to produce a `∀` proposition. Generalization utilizes `Intro_` mechanics a lot. 
- Instantiation, the reverse of generalization, turning a `∀` into an "any". 

By "different ways", we mean they are separately supported by distinguish primitive propositions and is not inferred from one or another. Also note that the above procedure doesn't involve typing, which is ignored in our project.

PM uses all these rewrites in a more systematic way to produce a proof, which we call *bottom-up construction*.

### Bottom up construction
The whole procedure can be splitted into 4 steps:
1. Start with a theorem as a template, and substitute its variables into some expressions
2. Apply `MP`/`Syll` for necessary alternations, for example, `P ↔ Q` to `Q ↔ P`
3. Generalize on a variable as soon as possible, when the correct form for its expression has manifested
4. Repeat 2 and 3 until all variables are being generalized and the statement has become a proposition

One can easily verify it's also the nature of *forward reasoning* building up a proof tree building up a proof tree from "leaves" to the "root". Note that this doesn't involve *typing* for PM, which is ignored in this project.

**Implementation-wise, `MP` alone is very limited:** it only works on the whole expression, but not for sub-expressions. There are many way to get rid of this problem: syllogism is already a specific case for sub expression on MP; But what if, I have propositions of the form of `P ↔ (Q → R)` and `Q`? We can view theorems in chapter 1 - 5 as common specific cases for MP to fit in and apply; chapter 9 and beyond tries to generate their *equivalent* - soon will be called *variants* later - when a new symbol has been introduced in.

## `rewrite/setoid_rewrite`
**We use `rewrite` to patch the `MP`.** Consider the following case: if we have a proposition of `P ↔ Q` and want to `MP` on it with `P`, we might *destruct* the proposition into `(P → Q) ∧ (Q ∧ P)`, then destruct on `∧` to perform the MP. While `→` propositions are such tedious to deal with, `↔` seems to be way more easier with our Rocq's default `rewrite`. Sometimes to produce a shorter proof, when `→` and `↔` version of a theorem both exist, we will adapt to the `↔` version with `rewrite`. Note that syllogism isn't `rewrite`, as it's performed on `→`.

**But the power of `rewrite` is still very limited.** It works mostly when the whole expression is of the form `P → Q`, plus a few exceptions. Taking the `P ↔ (Q → R)` as example, we will not be able to rewrite `Q → R` into `Q → S` if we provide `R → S`.

**To fix this, we use `setoid_rewrite` to patch `rewrite`.** `setoid_rewrite` is the *generalized rewriting* of Rocq. It has been very useful to rewrite a sub expression connected by `→`, or wrapped up within a `∀`.

**Yet again, `setoid_rewrite` has its limitation. For `=`, we start to patch with a *variant*.** Definitional equality is undefined(p.94) in PM, leaving us to freely design how to perform the rewrite on them. We set the equivalence *variant* in `TOOLS` section, when we need to use a definitional equality. A typical example will be like this:

```coq
(* The original version of `Impl1_01` *)
Definition Impl1_01 (P Q : Prop) : (P → Q) = (¬ P ∨ Q). Admitted.

Theorem x : (* ... *).
Proof.
  (* TOOLS *)
  (* The equiv variant for `Impl1_01`, where definitional equality has been replaced into a `↔` *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
Qed.
```

Notes:
- `eq_to_equiv` in `lib.v` is intended to be the reverse of `propositional_extentionality`, since it's more convenient to use.
- During our formalization, there is also rare case where we need for *functional extentionality*, by using `extentionality` tactic or `f_equal`.

## Polymorphism and the variant mechanic
We call the above example a *variant*, so that we can manually settle down a pattern as a similar proposition, with extra feature adjusted. We perform them manually, because we don't have enough clues to automate them.

**There are other cases where we need to patch with variants:** PM might expect you to automatically generate the belows.
1. The same proposition where argument `X` is lifted from elementary proposition to 1-order proposition, 2-order proposition, and so on
2. The same proposition where `f x` has become `f x y` with an extra argument provided
3. The same proposition where argument `X` is lifted from just an individual to a type of specific symbol, e.g. from proposition to class

**Case 1 above gives us the intuition to utilize *polymorphism***. As a initial attempt, we design the `Order n` hierarchy to simulate functions of different orders.

**Case 2's polymorphism is orthogonal to case 1.** The polymorphism goes "vertically", but doesn't go "horizontally" as in our case 2. Our initial take at polymorphism in this direction is the `Order2` type. It extends the argument length just by one. This example results into our preference to *manually* pick types for each of the arguments, choose which `Order` to use, how many arguments a function have, and postfix the names with `_pred`. See [naming convention](./contribution_guide/style_guide.md) for further details.

**Case 3 requires a different hierarchy constructed on *new symbols***. Here we take chapter 20 as the example. Chapter 20 is the first chapter introducing such symbol, that we have to manually assign with a `Class.t` type. As a conservative take, there might be even more hierarchies on other symbols. To generalize between `Class.t` and `Prop`, the best candidate is just an an arbitrary type `A`. It's easy to see that, polymorphism in this direction is orthogonal to the `Order`'s direction. Sometimes when designing the variants, we might postfix with, for example, `_class` for the theorems.

**We use arbitrary type `A` to compose symbols.** Chapter 14 has introduced the `iota` notation, but it soon reveals in chapter 20 that `iota`s not only work on `Prop`s, but also on `Class`es. This constitutes to another motivation where we need to generalize between `Class` and `Prop`.

**There is an orthogonal polymorphism that `A` cannot resolve.** As mentioned in [mechanics](./3_mechanics.md/#chapter-20), sometimes we have to *expose the interpretation beneath the language* by assigning a class variable with an associated function. PM has several defects on such treatment, and we are supposing that... 

**Russell hasn't distinguished between his language and interpretation**. We are witnessing numerous examples in chapter 20 in particular. As we're currently designing class as `Alpha := ^z => FAlpha z` for some function `FAlpha`, we will call `Alpha` the representation of a *class variable*, while `FAlpha` the *underlying function*. Through proofs in the book we can observe several facts:
- While \*20.21 is using `alpha` as its representation of class, \*20.55 want to use it when it has been instantiated into a function
- \*20.42 associates `Psi` with `Alpha` without explicitly mentioning such association
- \*20.53, while only uses `Alpha` in its representation, automatically 
- \*20.61 has explicitly stated its variant to switch between its class variable and its underlying construction with function
- One can also consider, if for our current design, `FAlpha` turns out to be some `Class.t A → Prop`, and for that exclusive `Class.t A` instance we didn't provide its underlying function.
- Even a level down, sometimes PM will cite a theorem from interpretation, while it should be used otherwise.

**Because of the lacking of association, some of our theorems use `let` as a result.** See example below, and related [mechanics](./3_mechanics.md/#chapter-20)/[naming convention](./contribution_guide/style_guide.md) part.
```Coq
Theorem associating_function_to_class (FAlpha : Prop → Prop) :
  let (Alpha := ^z => FAlpha z) in
  (* ... *)
  .
```

There are cases where `let` still doesn't cover. As our experimental attempt, axiom `class_func_associate` is being used for such rare case, to manually declare association between two functions in a proof.

**We cannot use `A` to cover hierarchies of different symbols.** `A` can generalize a single type of `Class` and `Prop`, but not the *hierarchies* between them. Our implementation has not address anything about this, and this will be discussed in [suggestion](./_6_suggestion.md).

Implementation wise, we can view `Class` hierarchies as one "supplementary" hierarchy in the text. Another supplementary hierarchy that should be useful to mention, is our attempt at distinguishing *untyped functions*. Simply put, we wanted to use `Order x → Prop` to mean a predicative function, while `(Prop → Prop) ... → Prop` means it's untyped function. This works prior chapter 14, but has lost its functionality completely in chapter 20, creating an unnecessary chaos. See \*20.112 for such an unavoidable failure as our attempt.

To summarize: we are witnessing that there are many dimensions for us to generalize, which is not just simply a polymorphism. To uniquely *type* a term in PM, we have to consider the hierarchies listed below:

| Type of hierarchy      | Base case                                 | Higher order case                |
|------------------------|-------------------------------------------|----------------------------------|
| **Primary**            | -                                         | -                                |
| proposition            | atomic symbol                             | total generalization of matrix   |
| propositional function | 0-order matrix                            | partial generalization of matrix |
| **Supplementary**      | -                                         | -                                |
| matrix                 | atomic symbol                             | predicative functions            |
| class                  | description-like construction on function | inferred from function           |
| untyped functions      | Rocq type `Prop → Prop`                  | `(...(Prop → Prop)...) → Prop` |

**Table 4.2: Discovered hierarchies in Principia Mathematica**

## Simplification and debugs
**Chores.** Occasionally, we want to even further simplify the proof down, because:
- We can clearly provide its equivalent routine using PM theorems
- We have torturing urge to simplify the proofs. Check out `n11_71` to appreciate its ridiculous length.

Below is a table for some of the simplifications we might used, but some of them might never appear in the proofs. This is because unless there is a severe technical barrier, they are **recommended** to be taken down. 

| Feature to implement        | Tactic                                     |
|-----------------------------|--------------------------------------------|
| `Hp`                        | `intro Hp`+`pose proof (Sn Hp) as S`\[\*\] |
| `Simp` theorems' equivalent | `destruct Sn as [Sn _]`                    |
| Necessary alpha conversion  | `replace...with`, `simpl`, etc.            |
| Reorganize the proof window | `move`, `clear`, etc.                      |
| Others                      | Addressed with comments in code            |

\[\*\]: Mandatory when PM uses `Hp` in its proof. When a `Hp` has appeared in the text, we find out that the theorems PM cites have a high chance to be working *exactly* on the conclusion after `Hp`, although with a lot of exceptions as well. In general, we still think that use `Hp` to abstract away the premise matches up nicely with how PM applies the theorems.

While all above tactics have covered the essentials for presenting the proof, the actual development involves serious debugs that might use more tactics than above. See [debugging proof](./contribution_guide/debugging_proof) for a guidance on actual development. Tactics for debugging is **required** to be reduced to minimum when we have finished them.
