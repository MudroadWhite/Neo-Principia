# Tactics
As mentioned in previous chapters, we "just `pose` and `rewrite`". This chapter is going to expand the slogan in complete details.

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

**Table X: Full PM features considered and their implementations in Rocq**

## How do we assert a proposition is true?
The story starts with a very simple beginning. To assert a cited theorem is true, we `pose` a proof, which is pretty fundamental in Rocq. Voila.

If we only perform such a `pose`, the proof window is logically correct, but *visually* awful. We not only have the proof, but also the proof terms. However, we are not doing backward reasoning, nor do the proof term correctly reflect the construction when we are using a lot of `setoid_rewrite`, being introduced in later section. We choose to leave `pose proof` the only candidate to present a citation.

`pose proof` successfully presents a proposition in the hypothesis window, but it doesn't solve a goal. `apply` allows us to solve the goal automatically with a theorem. `now` allows us to solve the goal as soon as we have deduced the right proposition. `exact`, as mentioned in the [architecture](./2_architecture.md), is exclusively used to hint that we have covered all steps in a proof to conclude a `Qed`.

The iceberg under theorems in Principia Mathematica still extends, as their nature is actually quite different from typical theorems you see. All theorems are actually *propositional function*s in Principia, and you never see a real "proposition". *Proposition function*(TODO: move this part into `mechanics`) means that propositional variables will not be fixed in number, and arbitrarily new variables can be introduced in between every proof steps, just like a function closure.

If we are using Rocq's *function* to interpret the theorems in Rocq, a proof will look like this: 

```Coq
(* Assuming there is a `Asserted` predicate for arbitrary Rocq functions *)
Theorem prop_func_theorem_example : Asserted (fun P => P -> P).

Theorem prop_func_proof_example : Asserted (fun P Q => (P /\ Q) -> (P /\ Q)).
Proof.
  assert (S1 : Asserted (fun P => P -> P)).
  { apply prop_func_theorem_example. }
  assert (S2 : Asserted (fun P Q R => (P -> Q) -> (Q -> R) -> (P -> R))).
  { (* ... *) }
Admitted.
```
While this example is actually speaking about nonsense, notice how an extra `R` can be presented as a legit variable, which is not being introduced as a variable of `prop_func_proof_example`. Such phenomenon seems absurd, but commonly appears in all the proof of PM.

Our implementation didn't use the interpretation above. First, this is an interpretation just came up when I'm writing the documentation right now. Second, with functions as interpretation for PM's propositional functions, we still have to consider how it works with other symbols: functions might be harder to manipulate than propositions. For example, how do you make sure the `x` in different step of proof is the same `x`? How will this interpretation limit your situations to substitute `x` into some more complicated expressions? How should we proceed with definitional equality `=`'s substitution within this interpretation?



 We are allowed to set up arbitrarily more propositional "variables", corresponded to the *real variable*s in PM, and are actually constants that cannot be substituted; they must only to be introduced in the `TOOLS` section at the beginning of the proof. These "real" variables are mostly for being *generalized* into a quantified apparent variable, the `x` in a `forall x`. This is being done by a series of axioms in `lib.v`, prefixed with `Intro_`.

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

Just like `rewrite`, `setoid_rewrite` isn't always working. The biggest part of its defect arisen from treatment with `=`. Definitional equality, on the other hand, is undefined(p.94), leaving us to freely design how to perform the rewrite on them. We set the equivalence *variant* in `TOOLS` section, when we need to use a definitional equality. A typical example will be like this:

```coq
(* The original version of `Impl1_01` *)
Definition Impl1_01 (P Q : Prop) : (P → Q) = (¬ P ∨ Q). Admitted.

Theorem x : (* ... *).
Proof.
  (* TOOLS *)
  (* The equiv variant for `Impl1_01`, where definitional equality has been replaced into a `<->` *)
  set (λ P0 Q0 : Prop, eq_to_equiv (P0 → Q0) (¬ P0 ∨ Q0) (Impl1_01 P0 Q0))
    as Impl1_01a.
  (* ******** *)
Qed.
```

Notes:
- `eq_to_equiv` in `lib.v` is intended to be the same as `propositional_extentionality`, but more convenient to use.
- During our formalization, there is also rare case where we need for *functional extentionality*, by using `extentionality` tactic or `f_equal`.

## Variants, symbol polymorphism and theorem polymorphism
And yes, even after arriving that far, we still have not covered the complete cases of when do we need to perform a *rewrite*; and there are still many cases where `setoid_rewrite` doesn't work. For example, PM might expect you to automatically generate:
- The same proposition where `f x` has become `f x y` with an extra argument provided
- The same proposition where argument `X` is lifted from elementary proposition to 1-order function, 2-order function, and so on
- The same proposition where argument `X` is lifted from just an individual to a type of specific symbol, e.g. from proposition to class


TODO:
- different types: order, A -> prop, type of symbol(also mentioned by Randall)

TODO: 
- Lacking of distinction between language and interpretation

## Others
- `Simp` and `destruct Sn as [Sn _]`
- `Hp` and `pose proof S`

TODO: 
- put simplification at the end of the chapter
- gather simplification examples in chapter 9 & 10

## Simplification(TODO: and debugs?)
TODO: 
We can use a new tactic to simplify a tedious part of proof, if
- We can clearly provide its equivalent routine using PM theorems
- We clearly identified the types of parameters, for theorems in original routine. Parameters' types matter
- We have torturing urge to simplify the proofs. Check out `n11_71` to appreciate its ridiculous length.

Either for "historical reasons"(this project really doesn't have a history), or when we want to work through a proof quickly, and we didn't figure out the correct way to write the proof, "technical hacks" arises for proof completions. The most common ones are listed below, but they might never appear in the proofs. This is because: unless there is a severe technical barrier, they are **recommended** to be taken down.
- \[Simplification\]`replace...with` is a valid and flexible substitution for rewriting, but it's too heavy.
- \[Simplification\]`apply propositional_extentionality` might occur inside `replace...with` blocks. Its purpose is to change the goal of `=` form into a goal of `↔` form for easier reasoning. It might work against original text.
- \[Simplification\]`intro` introduces the premise as a hypothesis. `intro Hp`, as utilized in chapter 5 & 10, has proven its harmlessness. Other from `intro Hp`, other occurrences should be eliminated. The proposition `S` to be applied to, has to be replaced completely with `pose proof (S Hp) as S`.
- \[Simplification\]`now tactic thm ...` says that, if the `tactic` we use can directly provide a result that is not very far from the goal, then we prove the goal immediately. Typically it's very useful for saving a line of `exact thm`. Every line of `now tactic thm` can be turned back into `tactic thm` for readers to check if it does indeed generate a proposition that is exactly the same as the goal, and this tactic is **recommended** to use.
- \[Simplification\]Further exceptions not being listed above, for example in chapter 11, have to be explicitly stated with a comment that a simplification has happened. This is **recommended** to be taken down in the future.

## Debugging
While all above tactics have covered the essentials for presenting the proof, the actual development involves serious debuggings that might use more tactics than above. See [debugging proof](./contribution_guide/debugging_proof) for a guidance on actual development.

- Tactics for debugging is **required** to be reduced to minimum when we have finished them.
