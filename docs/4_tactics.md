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
| Symbol interpretation                                           | `let` clause + TODO mechanic                    |
| **Part 2: Computation**                                         | -                                               |
| Stepping forward                                                | `assert`                                        |
| Conclude a step/a proof                                         | `apply`+`now`/`exact`                           |
| Asserting a proposition                                         | `pose proof` only                               |
| Rewriting on a proposition                                      | "PM-based" tactics or `rewrite`/`setoid_rewrite`|
| `=` rewriting                                                   | `eq_to_equiv`+`setoid_rewrite`                  |

**Table X: Full PM features considered and their implementations in Rocq**

## How do we assert a proposition is true?
**The story starts with a very simple beginning.** To assert a cited theorem is true, we `pose` a proof, which is pretty elementary in Rocq. Voila.

**`pose proof` is the only candidate to prettify the `pose`.** The `pose` can ensure the proof window logically correct, but *visually* awful. Proof terms will take away a large part of space, before the type of terms come into our view. We are not doing backward reasoning, nor are these proof terms meaningful - we will use a lot of `setoid_rewrite`, being introduced in later section.

**We then add some tactics to conclude a proof.** `pose proof` doesn't solve a goal. `apply` allows us to solve the goal automatically with a theorem. `now` allows us to solve the goal as soon as we have deduced the right proposition. `exact`, as mentioned in the [architecture](./2_architecture.md), is exclusively used to hint that we have covered all steps in a proof to conclude a `Qed`.

**Yet PM's theorems are not propositions.** They are actually *propositional function*s in Principia, and you almost never see a real "proposition". The nature of *proposition function*(TODO: move this part into `mechanics`) allows arbitrarily new variables to be introduced in between every proof steps, just like a function closure. See below example: here's how it will look like if we are using Rocq's *function* to interpret the theorems in Rocq.

```Coq
(* Assuming there is a `Asserted` predicate for arbitrary Rocq functions *)
Theorem prop_func_theorem_example : Asserted (fun P => P → P).

Theorem prop_func_proof_example : Asserted (fun P Q => (P ∧ Q) → (P ∧ Q)).
Proof.
  assert (S1 : Asserted (fun P => P → P)).
  { apply prop_func_theorem_example. }
  assert (S2 : Asserted (fun P Q R => (P → Q) → (Q → R) → (P → R))).
  { (* ... *) }
Admitted.
```
While this example is actually speaking about nonsense, notice how an extra `R` can be presented as a legit variable, which is not being introduced as a variable of `prop_func_proof_example`. Such phenomenon seems absurd, but commonly appears in all the proof of PM.

TODO: address prop function's nature better in `mechanics`

**And in reality, we ignore the nature of proposition function.** First, this is an interpretation just came up when I'm writing the documentation. Second, with functions as interpretation for PM's propositional functions, we still have to consider how it works with other symbols: functions might be harder to manipulate than propositions. For example, how do you make sure the `x` in different step of proof is the same `x`? How will this interpretation limit your situations to substitute `x` into some more complicated expressions? How should we proceed with definitional equality `=`'s substitution within this interpretation?

**Instead, we are using *propositions* to model propositional functions,** while simulating the feature to set up arbitrarily more propositional "variables" - actually constants that cannot be substituted; they must only to be introduced in the `TOOLS` section at the beginning of the proof. These "real" variables are mostly for being *generalized* into a quantified apparent variable, the `x` in a `∀ x`. This is being done by a series of axioms in `lib.v`, prefixed with `Intro_`. The complete method to use `Intro_` in the proof is `set (X := Intro_ ...)`, available everywhere in the proof files as the identifier of *the `Intro` mechanic*.

**There is yet another problem for us to consider in PM.(TODO: extend this part)** As analyzed in `mechanics`(TODO: add doc in ch14/20 and add link), since we didn't design an AST yet, we are assuming that symbols in PM combines with each other. Symbols can have different types, e.g. `∀ alpha : Class.t` is different from `∀ x : Prop`, so these symbols have to be "polymorphic". For chapter 20, it turns out further that symbols like *classes* might not exist solely; they will have to come with an underlying interpretation by default(TODO: mention this somewhere in the text), and when can we assign a function to a class has completely no specification in PM. If we come to that case, we will use the following syntax(TODO: move this into chapter 20?):

```Coq
Theorem associating_function_to_class (FAlpha : Prop → Prop) :
  let (Alpha := ^z => FAlpha z) in
  (* ... *)
  .
```

## How do we rewrite a proposition?
**PM should only use modus ponens** to its ideal. It starts with \*1.11, but generalize manually to more cases once a new notion/symbol has been introduced into a chapter. Therefore, each chapter will contain a *modus ponens* equivalent, whenever necessary.

***modus ponens* isn't the only mechanic to get a new proposition.** In particular, *quantified propositions* are only constructed by another mechanic: *generalization* on a variable in a "proposition"(that actually turns out to be a prop function). Same as *modus ponens*, whenever a new symbol has been introduced in, the chapter will have a `Pp`/`Thm` of its equivalent, either assumed or deduced from previous chapters.

*Generalization* utilizes our `Intro_` pretty frequently, but not restricted to `Intro_`. It says:
- If we have a real variable *X* in a proposition (still as usual, turns out to be propositional function) `Phi X`
- Then we can make a proposition `∀ x, Phi x`, occasionally with some type checks

***Generalization* is implemented as a *proposition* utilizing `MP`.** Within which, `n10_11` being the most commonly used ones. In principle, there should be better ways to perform the generalization.

But how about all other propositions in general? How will they manifest, and how are they being constructed?

### Bottom up construction
The whole procedure of a valid proposition can be splitted into 4 steps:

1. Start with a theorem as a template, and substitute its variables into some expressions
2. Apply `MP`/`Syll` for necessary alternations, for example, `P ↔ Q` to `Q ↔ P`
3. Generalize on a variable as soon as possible, when the correct form for its expression has manifested
4. Apply `MP`/`Syll` for the rest of the alternations. It usually involves building more sub expressions into the expression, for example from `P` to `P ∧ P → P`.

Which is what we called *bottom-up construction* by the logical connectives appeared in a proposition. One can easily verify it's also the nature of *forward reasoning* building up a proof tree building up a proof tree from "leaves" to the "root".

**Here is a huge fallback for `MP` alone:** it can only be performed on the whole expression, but not for sub-expressions. There are many way to get rid of this problem: syllogism is already a specific case for sub expression on MP; But what if, I have propositions of the form of `P ↔ (Q → R)` and `Q`? We can view theorems in chapter 1 - 5 as common specific cases for MP to fit in and apply; chapter 9 and beyond tries to generate their *equivalent* - soon will be called *variants* later - when a new symbol has been introduced in.

## `rewrite/setoid_rewrite`
**`rewrite` is how we patch the proofs in this project.** Consider the following case: if we have a proposition of `P ↔ Q` and want to `MP` on it with `P`, we might *destruct* the proposition into `(P → Q) ∧ (Q ∧ P)`, then destruct on `∧` to perform the MP. While `→` propositions are such tedious to deal with, `↔` seems to be way more easier with our Rocq's default `rewrite`. Sometimes to produce a shorter proof, when `→` and `↔` version of a theorem both exist, we will adapt to the `↔` version with `rewrite`. Note that syllogism isn't `rewrite`, as it's performed on `→`.

TODO: gather simplification examples in chapter 9 & 10

**Still, the power of `rewrite` is limited.** It works mostly when the whole expression is of the form `P → Q`, plus a few exceptions. Taking the `P ↔ (Q → R)` as example, we will not be able to rewrite `Q → R` into `Q → S` if we provide `R → S`.

**To fix this, we introduce `setoid_rewrite`,** the *generalized rewriting* of Rocq. It has been very useful to rewrite a sub expression connected by `→`, or wrapped up within a `∀`.

**But `setoid_rewrite` isn't always working as well. For `=`, we will need extra treatments.** Definitional equality is undefined(p.94) in PM, leaving us to freely design how to perform the rewrite on them. We set the equivalence *variant* in `TOOLS` section, when we need to use a definitional equality. A typical example will be like this:

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
And even after arriving that far, we still have not covered the complete cases of when do we need to perform a *rewrite*; and there are still many cases where `setoid_rewrite` doesn't work. For example, PM might expect you to automatically generate:
1. The same proposition where argument `X` is lifted from elementary proposition to 1-order function, 2-order function, and so on
2. The same proposition where `f x` has become `f x y` with an extra argument provided
3. The same proposition where argument `X` is lifted from just an individual to a type of specific symbol, e.g. from proposition to class

Designing a similar proposition with extra feature adjusted will be called as designing a *variant*. We can soon make a conclusion that *variant* cannot be easily resolved in a unified and single way.

The story of *variant*s thus start from a concept mostly common to programmers: polymorphism. For our case 1, polymorphism seems to be simple: we have already designed a `Order n` hierarchy to simulate functions of different orders. However, such polymorphism goes "vertically", but doesn't go "horizontally" as in our case 2. 

For case 2, `Order` simply fails. We design a new `Order2` manually to express such polymorphism. When a theorem is supposed to be lifted in the direction of 1 & 2, we prefer to be conservative: we don't know yet what will happen after chapter 20. We are requiring to design a proposition *variant*, mostly postfixed with `_pred`, that has *fixed order* for every necessary order we need.

TODO: mention extra types for symbols, by Randall
- since there is a hirrarchy of class, these extra type should be constructed

The actual phenomenon behind case 3, is a different hierarchy constructed on *new symbols*. Chapter 20 is the first chapter introducing such symbol, but we won't know if there are any other hierarchies based on other symbols. An element of type `Class` is definitely neither an element of type `Prop` or type `Order n`. Our current implementation is generalizing all these into an arbitrary type `A`.

Even if we have resolved such conflict at 1st level of different hierarchies, what will it happen at higher levels? So far we didn't resolve such conflict, and it will be discussed in [audit](./5_audit.md).

## Simplification and debugs
Occasionally, we want to even further simplify the proof down, because:
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

TODO: symbol association 
- does it have anything to do with hierarchy?
- mention its incompatability