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
| Symbol interpretation                                           | `let` clause + explicit interpretation mechanic |
| **Part 2: Computation**                                         | -                                               |
| Stepping forward                                                | `assert`                                        |
| Conclude a step/a proof                                         | `apply`+`now`/`exact`                           |
| Asserting a proposition                                         | `pose proof` only                               |
| Rewriting on a proposition                                      | "PM-based" tactics or `rewrite`/`setoid_rewrite`|
| `=` rewriting                                                   | `eq_to_equiv`+`setoid_rewrite`                  |

**Table X: Full PM features considered and their implementations in Rocq**

## How do we assert a statement is true?
**The story starts with a very simple beginning.** To assert a cited theorem is true, we `pose` a proof, which is pretty elementary in Rocq. Voila.

**`pose proof` is the only candidate to prettify the `pose`.** The `pose` can ensure the proof window logically correct, but *visually* awful. Proof terms will take away a large part of space, before the type of terms come into our view. We are not doing backward reasoning, nor are these proof terms meaningful - we will use a lot of `setoid_rewrite`, being introduced in later section.

**We then add some tactics to conclude a proof.** `pose proof` doesn't solve a goal. `apply` allows us to solve the goal automatically with a theorem. `now` allows us to solve the goal as soon as we have deduced the right proposition. `exact`, as mentioned in the [architecture](./2_architecture.md), is exclusively used to hint that we have covered all steps in a proof to conclude a `Qed`.

**Sometimes, the proof further involves extra variables.** See for example \*9.37, adding a new real variable in the middle of the proof, just to be *generalized* in the future. To resolve this, we add a series of axioms in `lib.v`, prefixed with `Intro_`, and add a line of `set (X := Intro_ ...)` in the `TOOLS` section. This is called the `Intro` mechanic. Without the `Intro` mechanic, intermediate statements cannot be normally asserted.

## How do we rewrite a proposition?
**PM is supposed to only use modus ponens** to its ideal. It starts with \*1.11, but generalize manually to more cases once a new notion/symbol has been introduced into a chapter. Therefore, each chapter will contain a *modus ponens* equivalent, whenever necessary.

***Generalization* is another way to produce a new proposition.** In particular, *quantified propositions* are only constructed through: *generalization*, being explained in [mechanics](./3_mechanics.md). Generalization utilizes `Intro_` mechanics a lot. Similar to MP, PM also extend generalize for each symbols in each of the chapters.

### Bottom up construction
**Besides quantified propositions, how do we produce a proposition in general?** The whole procedure can be splitted into 4 steps:
1. Start with a theorem as a template, and substitute its variables into some expressions
2. Apply `MP`/`Syll` for necessary alternations, for example, `P ↔ Q` to `Q ↔ P`
3. Generalize on a variable as soon as possible, when the correct form for its expression has manifested
4. Apply `MP`/`Syll` for the rest of the alternations. It usually involves building more sub expressions into the expression, for example from `P` to `P ∧ P → P`.

**We call this *bottom-up construction*** by the logical connectives appeared in a proposition. One can easily verify it's also the nature of *forward reasoning* building up a proof tree building up a proof tree from "leaves" to the "root".

**However, `MP` alone is very limited:** it only works on the whole expression, but not for sub-expressions. There are many way to get rid of this problem: syllogism is already a specific case for sub expression on MP; But what if, I have propositions of the form of `P ↔ (Q → R)` and `Q`? We can view theorems in chapter 1 - 5 as common specific cases for MP to fit in and apply; chapter 9 and beyond tries to generate their *equivalent* - soon will be called *variants* later - when a new symbol has been introduced in.

## `rewrite/setoid_rewrite`
**`rewrite` is how we patch the proofs beyond `MP`.** Consider the following case: if we have a proposition of `P ↔ Q` and want to `MP` on it with `P`, we might *destruct* the proposition into `(P → Q) ∧ (Q ∧ P)`, then destruct on `∧` to perform the MP. While `→` propositions are such tedious to deal with, `↔` seems to be way more easier with our Rocq's default `rewrite`. Sometimes to produce a shorter proof, when `→` and `↔` version of a theorem both exist, we will adapt to the `↔` version with `rewrite`. Note that syllogism isn't `rewrite`, as it's performed on `→`.

TODO: gather simplification examples in chapter 9 & 10

**But the power of `rewrite` is still very limited.** It works mostly when the whole expression is of the form `P → Q`, plus a few exceptions. Taking the `P ↔ (Q → R)` as example, we will not be able to rewrite `Q → R` into `Q → S` if we provide `R → S`.

**To fix this, we introduce `setoid_rewrite`,** the *generalized rewriting* of Rocq. It has been very useful to rewrite a sub expression connected by `→`, or wrapped up within a `∀`.

**Yet again, `setoid_rewrite` has its limitation. For `=`, we start to patch with first kind of *variant*.** Definitional equality is undefined(p.94) in PM, leaving us to freely design how to perform the rewrite on them. We set the equivalence *variant* in `TOOLS` section, when we need to use a definitional equality. A typical example will be like this:

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
- `eq_to_equiv` in `lib.v` is intended to be the same as `propositional_extentionality`, but more convenient to use.
- During our formalization, there is also rare case where we need for *functional extentionality*, by using `extentionality` tactic or `f_equal`.

## Polymorphism and the variant mechanic
**And there are still so many cases besides that "variant".** For example, PM might expect you to automatically generate:
1. The same proposition where argument `X` is lifted from elementary proposition to 1-order proposition, 2-order proposition, and so on
2. The same proposition where `f x` has become `f x y` with an extra argument provided
3. The same proposition where argument `X` is lifted from just an individual to a type of specific symbol, e.g. from proposition to class

**We design other *variants* for each of these cases.** Designing variant is designing a similar proposition with extra feature adjusted. We can soon make a conclusion that *variant* cannot be easily resolved in a unified and single way.

**Case 1 above gives us the intuition to utilize *polymorphism***. As a result, we design the `Order n` hierarchy to simulate functions of different orders.

**However, such polymorphism simply fails for case 2.** The polymorphism goes "vertically", but doesn't go "horizontally" as in our case 2. Our initial take at polymorphism in this direction is the `Order2` type. It extends the argument length just by one.

**As a conservative take, we design *monomorphic* theorem variants.**  When designing a proposition *variant*, we will manually pick types for each of the arguments, choose which `Order` to use, how many arguments a function have, and postfix the names with `_pred`. See [naming convention](./contribution_guide/style_guide.md) for further details. As there seems to be too many factors to determine when writing the variant, we didn't try to further automate the design.

TODO: mention extra types for symbols, by Randall; since we have observed the class hierarchy of class, extra type is highly suggested

**Case 3 requires a different hierarchy constructed on *new symbols***. Here we take chapter 20 as the example. Chapter 20 is the first chapter introducing such symbol, that we have to manually assign with a `Class.t` type. As a conservative take, there might be even more hierarchies on other symbols. To generalize between `Class.t` and `Prop`, the best candidate is just an an arbitrary type `A`. It's easy to see that, polymorphism in this direction is orthogonal to the `Order`'s direction. Sometimes when designing the variants, we might postfix with, for example, `_class` for the theorems.

**Around the `A` polymorphism is how we compose the symbols.** Chapter 14 has introduced the `iota` notation, but it soon reveals in chapter 20 that `iota`s not only work on `Prop`s, but also on `Class`es. This constitutes to another motivation where we need to generalize between `Class` and `Prop`.

**Beneath the `A` polymorphism is also a whole new rabbit hole.** As mentioned in [mechanics](./3_mechanics.md/#chapter-20) (TODO: finish related part in chapter 20), sometimes we have to *expose the interpretation beneath the language* by assigning a class variable with an associated function. PM has several defects on such treatment, and we are supposing that... 

**Russell hasn't distinguished between his language and interpretation,**. We are witnessing numerous examples in chapter 20 in particular. As we're currently designing class as `Alpha := ^z => FAlpha z` for some function `FAlpha`, we will call `Alpha` the representation of a *class variable*, while `FAlpha` the *underlying function*. Through proofs in the book we can observe several facts:
- While \*20.21 is using `alpha` as its representation of class, \*20.55 want to use it when it has been instantiated into a function
- \*20.42 associates `Psi` with `Alpha` without explicitly mentioning such association
- \*20.53, while only uses `Alpha` in its representation, automatically 
- \*20.61 has explicitly stated its variant to switch between its class variable and its underlying construction with function
- One can also consider, if for our current design, `FAlpha` turns out to be some `Class.t A -> Prop`, and for that exclusive `Class.t A` instance we didn't provide its underlying function.
- Even a level down, sometimes PM will cite a theorem from interpretation, while it should be used otherwise.

**Because of the lacking of association, some of our theorems use `let` as a result.** See example below, and related [mechanics](./3_mechanics.md/#chapter-20)/[naming convention](./contribution_guide/style_guide.md) part.
```Coq
Theorem associating_function_to_class (FAlpha : Prop → Prop) :
  let (Alpha := ^z => FAlpha z) in
  (* ... *)
  .
```

**In addition, we are supposed to develop a mechanic to *explicitly interpret* the terms.** TODO: explicit interpretation for ch20

**...And we forgot to look upwards of the `A`.** We have just considered the case to generalize between `Class` and `Prop`. How about the *hierarchies* betwwen `Class` and `Prop`? Our implementation has not address anything about this, and this will be discussed in [suggestion](./_6_suggestion.md).

As a summary: we are witnessing that there are many dimensions for us to generalize, which is not just simply a polymorphism. We need polymorphism setups separately to:
- generalizes on orders
- generalize on argument lengths
- generalize between different types

And maybe most importantly: give a *unique type* to a term, so that types from these 3 hierarchies don't interfere with each other.

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

\[\*\]: Mandatory when PM uses `Hp` in its proof. TODO: explain why

While all above tactics have covered the essentials for presenting the proof, the actual development involves serious debugs that might use more tactics than above. See [debugging proof](./contribution_guide/debugging_proof) for a guidance on actual development. Tactics for debugging is **required** to be reduced to minimum when we have finished them.

TODO: place hierarchy table somewhere
| Type of hierarchy      | Base case                                 | Higher order case                |
|------------------------|-------------------------------------------|----------------------------------|
| **Primary**            | -                                         | -                                |
| proposition            | atomic symbol                             | total generalization of matrix   |
| propositional function | 0-order matrix                            | partial generalization of matrix |
| **Supplementary**      |                                           |                                  |
| matrix                 | atomic symbol                             | TODO: figure out                 |
| class                  | description-like construction on function | inferred from function           |

TODO: "originally, we use `prop -> prop` for impredicative funcs, `Order` for predicative funcs... issue in hierarchy in chapter 20