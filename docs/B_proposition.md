> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

The difference between a function and a proposition is scattered through Introduction's chapter I, II, III and chapter 1. As the first concepts being introduced in, the definition of a proposition is full of ambiguity. When figuring out the difference between a *proposition* and a *proposition built up from a function*, we have gathered below clues only to reveal how much is the chaos: 
- *Proposition* can be *asserted*. *Propositional function* also can be *asserted* by asserting any specific value by instantiating a function, and which, is a proposition.
- Asserted propositional function can still change its variable to produce different proposition asserted
- (\*2.02)However, when deducing on the proof, we can also perform substitution on asserted propositions. 
- Real variables, being revealed in later chapters, can be *generalized* into *apparent variables*, the variables of a `forall` or `exists`, for a proposition/function of higher order. See [chapter 9](./3_mechanics.md/#chapter-9) for meaning of generalization.
- When using theorem, `Phi X` can freely substitute into a propositional variable `P`, and *vice versa*.
- When we `Intro_` an extra variable, we din't find any generalization from letters of `P`, `Q`, `R`. Instead we always start from `X`, plus exceptions as functions.
- `P`, `Q`, `R` can still be substituted into forms like `Phi X`, but never a single `X`. 
- Everything asserted are *propositions*, while the modus ponens is mostly used as \*1.11 version for *propositional functions*
- We also 
- TODO: mention private conversation with Randall

Here is our attempt to make the most precise definition.

- **elementary propositions** contains no variables. They are strictly alphabets after `P`, `Q`, and so on, in chapter 2 - 5(p.91).
- **elementary functions** are propositions build up with *at least* one logical connectives. When a expression is identified as a function, atomic letters after `X` appeared in it are called *real variables*(p.19).

```Coq
(* This is an elementary proposition *)
Example example_ch1_proposition (P : Prop) := P.

(* This is an asserted elementary function value *)
Example example_ch1_prop_function_1 (φ : Prop) (X : Prop) := φ X.

(* This is the actual way to write the function, but we won't use it *)
Example example_ch1_prop_function_2 (φ : Prop) := fun (X : Prop) => φ X.
```

Our current conclusion is that we cannot identify the difference between *elementary proposition* and *elementary propositional function*. Higher order propositions and functions have more significant difference, will be revealed after [chapter 9](./3_mechanics.md/#chapter-9). In principle, we view everything in chapter 1 - 5 just as *propositions*, and elementary function manifests when we need to have a lambda term.


TODO: " It's strictly "not asserting a proposition"(p.18), but practically the same."


TODO: heavy analysis on what is a proposition

mention: there can be more interpretations;
TODO: read church's interpretation on PM

- ch1: *proposition* as an ambiguous text "consists of" *e-props* and *e-funcs*; we still prefer to call everything working on *propositions* for the rest of the text; rewrite parts on elementary functions
- ch1: *propositional functions* doesn't include identity function

- If it follows our guess, `forall` gets a proposition while `exists` is a propositional function

- https://plato.stanford.edu/entries/pm-notation/
- https://en.wikipedia.org/wiki/Glossary_of_Principia_Mathematica
- https://mathoverflow.net/questions/498078/what-is-the-consistency-strength-of-russell-whiteheads-principia-mathematica/498099#498099
