# Tactics
This chapter is targeted for the following topics:
- Identify between PM's native proofs and Rocq-specific simplified proofs
- List out *all* tactics we are using in the project

## Basic setup
Technically speaking, Principia's rewrite system is very simple, maybe much more simpler than most of the modern type systems, cf. [SEP entry for Principia Mathematica](https://plato.stanford.edu/entries/principia-mathematica/). All it cares about is 1. deducing a theorem either directly or from *modus ponens* and 2. substitute/*rewrite* subparts of a proposition according to some rules. Type is being defined and used in the system, but only partially, and untyped terms are still allowed to better express the ideas.

As mentioned in previous chapters, we "just `pose` and `rewrite`". Here we are going to expand the slogan in complete details.

| PM Feature                                                      | Implementation                                  |
|-----------------------------------------------------------------|-------------------------------------------------|
| **Part 1: Meta theory**                                         | -                                               |
| Pp and Df                                                       | Monomorphic Rocq `Definition`                   |
| Thm                                                             | Monomorphic Rocq `Theorem`                      |
| Real & Apparent variables                                       | lhs and rhs of a Rocq theorem                   |
| Functions                                                       | Rocq lambda calculus                            |
| General `∀`, `exists`, `<->` and other logical connectives      | Rocq's equivalent default                       |
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

**Table X: PM features considered and their implementations in Rocq**

## How do we assert a proposition is true?
The story starts with a very simple beginning. To assert a cited theorem is true, we `pose` a proof, which is pretty fundamental in Rocq. Voila.

If we only perform such a `pose`, the proof window is logically correct, but visually awful. We not only have the proof, but also the proof terms. However, we are not doing backward reasoning, nor do the proof term correctly reflect the construction when we are using a lot of `setoid_rewrite`. `pose proof` remains to be the only candidate to present a citation.

`pose proof` successfully present a proposition in the hypothesis window, but it doesn't solve a goal. `apply` allows us to solve the goal automatically.

However, theorems in Principia Mathematica is different from what typical theorems you will see. First of all, all theorems are actually the *propositional function*s in Principia, and you never see a real "proposition". By *proposition function*(TODO: move this part into `mechanics`) I mean, propositional variables will not be fixed, but can be arbitrarily introduced in just like a function closure. It would seem absurd but commonly used if we want to assert yet another propositional function, with more variables appeared in the theorem.

There are two ways to solve this problem. First one is interpreting the functions just as a lambda expression in Rocq: `(fun x => ...)`. However, by setting up every parameters inside the closure, we might lose many control or connections to them. For example, how do you make sure the `x` in different step of proof is the same `x`? How will this interpretation limit your situations to substitute `x` into some more complicated expressions? How should we proceed with definitional equality's substitution under this interpretation? These are actually something I have just brought up to when I write this document; that being said, this method is never tried in practice.

The second one is our current design. We are allowed to set up arbitrarily more propositional "variables", corresponded to the *real variable*s in PM, and are actually constants that cannot be substituted; they must only to be introduced in the `TOOLS` section at the beginning of the proof. These "real" variables are mostly for being *generalized* into a quantified apparent variable, the `x` in a `forall x`. This is being done by a series of axioms in `lib.v`, prefixed with `Intro_`.

The complete method to use `Intro_` in the proof is `set (X := Intro_ ...)`.

There is yet another problem for us to consider in PM. As analyzed in `mechanics`(TODO: add doc in ch14/20 and add link), since we didn't design an AST yet, we are assuming that symbols in PM combines with each other. Symbols can have different types, e.g. `forall alpha : Class.t` is different from `forall x : Prop`, so these symbols have to be "polymorphic". For chapter 20, it turns out further that symbols like *classes* might not exist solely; they will have to come with an underlying interpretation by default(TODO: mention this somewhere in the text), and when can we assign a function to a class has completely no specification in PM. If we come to that case, we will use the following syntax(TODO: move this into chapter 20?):

```Coq
Theorem associating_function_to_class (FAlpha : Prop -> Prop) :
  let (Alpha := ^z => FAlpha z) in
  (* ... *)
  .
```

## How do we rewrite a proposition?
In principal, PM's original design is only allowing proposition rewriting through one mechanic: *modus ponens*. It starts with \*1.11, but generalize manually to more cases once a new notion/symbol has been introduced into a chapter. Therefore, each chapter will contain a *modus ponens* equivalent, whenever necessary.

*modus ponens* isn't the only way to get a proposition. In particular, *quantified propositions* are only constructed by another mechanic: *generalization* on a variable in a "proposition"(that actually turns out to be a prop function). Same as *modus ponens*, whenever a new symbol has been introduced in, the chapter will have a `Pp`/`Thm` of its equivalent, either assumed or deduced from previous chapters.

*Generalization* utilizes our `Intro_` pretty frequently, but not restricted to `Intro_`. It says:
- If we have a real variable *X* in a proposition (still as usual, turns out to be propositional function) `Phi X`
- Then we can make a proposition `forall x, Phi x`, occasionally with some type checks

*Generalization*, `n10_11` being the most commonly used ones, is implemented as a *proposition* utilizing `MP`. In principle, there should be better ways to perform the generalization.

But how about all other propositions in general? How will they manifest, and how are they being constructed?

### Bottom up construction
The whole procedure of a valid proposition can be splitted into 4 steps:

1. Start with a theorem as a template, and substitute its variables into some expressions
2. Apply `MP`/`Syll` for necessary alternations, for example, `P <-> Q` to `Q <-> P`
3. Generalize on a variable as soon as possible, when the correct form for its expression has manifested
4. Apply `MP`/`Syll` for the rest of the alternations. It usually involves building more sub expressions into the expression, for example from `P` to `P /\ P -> P`.

Which is what we called *bottom-up construction* by the logical connectives appeared in a proposition. One can easily verify it's also the nature of *forward reasoning* building up a proof tree building up a proof tree from "leaves" to the "root".

Here is a huge fallback for `MP` appeared in this procedure: it can only be performed on the whole expression, but not for sub-expressions. There are many way to get rid of this problem: syllogism is already a specific case for sub expression on MP; But what if, I have propositions of the form of `P <-> (Q -> R)` and `Q`? We can view theorems in chapter 1 - 5 as common specific cases for MP to fit in and apply; chapter 9 and beyond tries to generate their *equivalent* - soon will be called *variants* later - when a new symbol has been introduced in.

## `rewrite/setoid_rewrite`
If we have a proposition of `P <-> Q` and want to `MP` on it with `P`, we might *destruct* the proposition into `(P -> Q) /\ (Q /\ P)`, then destruct on `/\` to perform the MP. As we are setting the `->`, `<->` as Rocq's default, another convenient way comes into our mind immediately: `rewrite`. `rewrite` is frequently used in this project, along with theorems in the form of `<->`. Sometimes to produce a shorter proof, when `->` and `<->` version of a theorem both exist, we will adapt to the `<->` version with `rewrite`. Note that syllogism isn't `rewrite`, as it's performed on `->`.

Still, the power of `rewrite` is limited. It can rewrite mostly when the whole expression is of the form `P -> Q`, plus a few exceptions. Still taking the `P <-> (Q -> R)` as example, we will not be able to rewrite `Q -> R` into `Q -> S` if we provide `R -> S`.

For this situation, `setoid_rewrite`, the *generalized rewriting* of Rocq has come into utilization. It has been very useful to rewrite a sub expression connected by `->`, or wrapped up within a `forall`.

TODO: `propositional_extentionality` or maybe `f_equal`; definitional equality is not defined, getting us insights on how to fix the rest

TODO:
- Lacking of distinction between language and interpretation
- different types: order, A -> prop, type of symbol(also mentioned by Randall)

TODO: put simplification at the end of the chapter
## Simplification(TODO: and debugs?)
TODO: 
We can use a new tactic to simplify a tedious part of proof, if
- We can clearly provide its equivalent routine using PM theorems
- We clearly identified the types of parameters, for theorems in original routine. Parameters' types matter
- We have torturing urge to simplify the proofs. Check out `n11_71` to appreciate its ridiculous length.

## Chapter 1 - 5
Proofs of these chapters are inherited from [Landon's work](https://github.com/LogicalAtomist/principia), simplified down so that they are using just the necessary tactics. 

### Proposing a proposition
`pose proof (thm x y z) as thm` should be almost the only way to *introduce* a theorem into the hypotheses, stating the existence of an already proven result. Also, starting from chapter 9, propositions are further come with a special kind of "type", basically the order of the proposition, and at base case we're only allowed to use elementary propositions as parameters, for elementary functions. That being said,
- `pose proof` on a theorem is **allowed**.
- `pose` on a theorem is strictly **not allowed**, because `pose proof` gets the proof window cleaner.
- Posed theorem is **required** be provided with all parameters at its *lhs*.
- \[Simplification\]Both `apply` and `exact` are **allowed** to use, if a goal can be solved immediately.

### Using a `→` theorem
A `→` theorem means that we can derive a conclusion from its premise. Immediately from above, here are almost the only allowed rules on `→` propositions:
- `MP p1 p2` is **allowed**, which uses the `MP` tactic on `p1` and `p2` being both propositions posed in the hypotheses. This is also how we treat "parameters" at the *rhs* of a theorem.
- `Syll p1 p2 Sy` is **allowed** for deriving a new "composed" proposition `Sy`, by using the `Syll` tactic. This tactic is similar to `MP` and its exact meaning is given in chapter 2.

### Using a `↔` theorem
Technically speaking, if we completely follow the deduction rules in PM's logic system, we need to
1. Apply `Equiv` theorem to destruct `P ↔ Q` into `P → Q ∧ Q → P`
2. Use `Simp` to extract the direction that you want to use
3. Prove properties from the extracted theorem using `MP` or `Syll`
4. Optionally get the result as `R → S` and `S → R`
5. Apply `Conj`, `Equiv` sequencially to combine them into `R ↔ S`

There's also a much more convenient routine provided in chapter 4, for `↔` rules to apply on `↔` propositions. 

It's straightforward that all these routines are quite a lot just for a single rewrite with `↔`. Rocq's `rewrite` tactic shrinks everything into one line, so we should use it providing that we can always expand these `rewrite`s into a sequence of `Simp`, `MP`, `Conj` and `Equiv`, or more.
- \[Simplification\]`rewrite` on `↔` is **allowed**, with explicit `->` or `<-` direction, optionally with `at` variant to specify the location for rewriting. Specifying the subterm to rewrite turns out to be a finite repetition of `MP`s and `Syll`s.
- The theorem for rewriting is **recommended** to provide its full (lhs) parameter list. Due to the complexity, we can generally omit the parameters after chapter 11.

Now that we finished discussing the construction routine on `↔`, we come to destruction routine on `↔`. `Equiv` theorem changes `P ↔ Q` back to `P → Q ∧ Q → P`. `Simp` picks the branch we want to use later, or we use both branch at different places. A more convenient way is seamlessly use Rocq's `destruct` tactic.
- \[Simplification\]`destruct` on `↔` is **allowed**.
- \[Simplification\]`destruct` is **required** to be further simplified into a `rewrite` on `↔`, if the `destruct`ed `↔` proposition branch is used for further `MP` or `Syll` on.
- `_` is **required** to eliminate unused `destruct` branches in place to keep the proof clean.

Explicit examples and comments on these simplifications are occasionally provided through chapter 9 & 10.

## Chapter 9 and beyond
It turns out that 1-order propositions are harder to be rewritten than the elementary propositions, and this is the first place where the Rocq tactic `setoid_rewrite` comes into usage.

### Using a definition
(p.94)Definitional equality(which is different from identity defined in chapter 13) is undefined in PM. Without specification, it seems like we can do whatever we want. For elementary propositions, Rocq's default preference `rewrite` works perfectly.
- `rewrite` on `=` is **allowed** with explicit `<-` and `->` direction. Same as above, `at` variant is **allowed**.
- Providing the parameter list is **recommended**.

When things become complicated, more problems will come to surface. A `∀ x` is enough to block the `rewrite` - it cannot identify the variable `x`. `setoid_rewrite` is an enhanced version of `rewrite` that can penetrate through `∀`s and `∃`s, with the drawback that it only works on `↔` relations. Hence the following rule:
- \[Simplification\]`eq_to_equiv` is **allowed** turn a `=` proposition into its `↔` equivalent. If we need to derive the quantified version of a `=` proposition, this becomes a necessity.
- \[Simplification\]`setoid_rewrite` on `↔` is **allowed** with explicit `<-` and `->` direction. Even if the `↔` doesn't come from `=`, this is a simplification.
- Similar to above, `at` variant for `setoid_rewrite` is **allowed**.
- Providing the full parameter list is **recommended**.

WARNING: Since `rewrite` is too convenient, even more than `MP` and `Syll`, `↔` theorems appear to be more useful than `→` theorems. In Rocq, we might *slightly overuse* `↔` theorems. Sometimes when a `→` theorem is enough to finish the proof, we might still choose a `↔` alternative and `rewrite` or `setoid_rewrite` with it.

#### What does `setoid_rewrite` actually simplify?
It should be very worthwhile to discuss how we deal with rewriting for quantified (`∀ x`) propositions, which also brings up the discussion on the viability for `setoid_rewrite` to simplify original proof. As we see, `setoid_rewrite` is only used in 2 situations: either the proposition is a `=`, or the proposition is a `↔`.

We first discuss the case for `↔`, starting with a question: how does a `∀` proposition appear? The basic idea for Principia is quite different from modern approach which uses a `∀` constructor. *Primitive propositions* in each chapter allow that
- If we have a proposition with the form of `φ X`, where `X` is a *real variable*, then
- We can change `φ X` into `∀ x, φ x`. Here, `x` has become an *apparent variable* as it's in a `∀`.
If, say, we want to construct something like `(∀ x, φ x) → (∀ y, ψ y)`, then we are supposed to have some other rules to allow us to "split" the `∀` into half. `∀ x, φ x → ψ x` can even be turned into `(∃ x, φ x) → (∃ y, ψ y)`.

Having a proposition with the form of `H : ∀ x, φ x`, plus a rewrite rule of `φ X ↔ ψ X`, we can 
1. Pick the rewrite rule `φ X ↔ ψ X` as our base
2. Use primitive propositions to generalize the base. For example it will become `(∀ x, φ x) ↔ (∀ x, ψ x)`.
3. Since the generalized rewrite rule rewrites `H` as a whole, we can rewrite `H` into `∀ x, ψ x`.

Even without `setoid_rewrite`, "rewriting on quantified propositions" is always viable with a fixed routine and a fixed set of primitive propositions to perform, and this is what exactly we're trying to use `setoid_rewrite` to do.

For `=` case: As stated above, how does `=` interact with others is undefined. Belows are some optional ways to get the works done. We can use `eq_to_equiv` or `apply propositional_extentionality` to change the `=` proposition into a `↔` one. An exceptional case is when we want to lift a `P = Q` relation to `∀ x, P x = ∀ x, Q x`: if we want to get a generalized version of `=` for direct `rewrite`, we might use `f_equal` to perform the lift.*

## Simplifications
Either for "historical reasons"(this project really doesn't have a history), or when we want to work through a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below, but they might never appear in the proofs. This is because: unless there is a severe technical barrier, they are **recommended** to be taken down.
- \[Simplification\]`replace...with` is a valid and flexible substitution for rewriting, but it's too heavy.
- \[Simplification\]`apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `↔` form for easier reasoning. It might work against original text.
- \[Simplification\]`intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from `intro Hp`, other occurrences should be eliminated. The proposition `S` to be applied to, has to be replaced completely with `pose proof (S Hp) as S`.
- \[Simplification\]`now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal, and this tactic is **recommended** to use.
- \[Simplification\]Further exceptions not being listed above, for example in chapter 11, have to be explicitly stated with a comment that a simplification has happened. This is **recommended** to be taken down in the future.

## Debugging
While all above tactics have covered the essentials for presenting the proof, the actual development involves serious debuggings that might use more tactics than above. See [debugging proof](./contribution_guide/debugging_proof) for a guidance on actual development.

- Tactics for debugging is **required** to be reduced to minimum when we have finished them.
