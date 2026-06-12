Appendix B: Definition of proposition in Principia Mathematica

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

The difference between a (elementary)function and a proposition is scattered through Introduction's chapter I, II, III and chapter 1. As the first concepts being introduced in, the definition of a proposition is full of ambiguity. When figuring out the difference between a *proposition* and a *proposition built up from a function*, we have gathered below clues only to reveal how much is the chaos: 
- *Proposition* can be *asserted*. *Propositional function* also can be *asserted* by asserting any specific value by instantiating a function, and which, is a proposition.
- Asserted propositional function can still change its variable to produce different proposition asserted
- (\*2.02)However, when deducing on the proof, we can also perform substitution on asserted propositions. 
- Real variables, being revealed in later chapters, can be *generalized* into *apparent variables*, the variables of a `forall` or `exists`, for a proposition/function of higher order. See [chapter 9](./3_mechanics.md/#chapter-9) for meaning of generalization.
- When using theorem, `Phi X` can freely substitute into a propositional variable `P`, and *vice versa*.
- When we `Intro_` an extra variable, we din't find any generalization from letters of `P`, `Q`, `R`. Instead we always start from `X`, plus exceptions as functions.
- `P`, `Q`, `R` can still be substituted into forms like `Phi X`, but never a single `X`. 
- Everything asserted are *propositions*, while the modus ponens is mostly used as \*1.11 version for *propositional functions*

On the other side, no material has identified what is exactly an elementary proposition. [Wiki](https://en.wikipedia.org/wiki/Glossary_of_Principia_Mathematica) simply doesn't have such an entry; [SEP](https://plato.stanford.edu/entries/pm-notation/) presents an alternative to be a modern reconstruction, that "would drastically alter the very content of the book". And I have also consulted with Randall Holmes about the definition; he has provide valuable insights on them, see [conversation](./A_conversation.md)

The final decision for us is just to present a guess, while leaving the implementation alone vague. Lack of definition will very much prevent further refinement: since you don't know the exact definition of elementary proposition, you're also unable to build the typing algorithm, from the very beginning. Still the general formalization looks already great, and everything compiles.

- **elementary propositions** contains no variables. They are strictly atomic alphabets after `P`, `Q`, and so on, in chapter 2 - 5(p.91).
- **elementary functions** are propositions build up with *at least* one logical connectives. When a expression is identified as a function, atomic letters after `X` appeared in it are called *real variables*(p.19).

```Coq
(* This is an elementary proposition *)
Example example_ch1_proposition (P : Prop) := P.

(* This is an asserted elementary function value *)
Example example_ch1_prop_function_1 (φ : Prop) (X : Prop) := φ X.

(* This is the actual way to write the function, but we won't use it *)
Example example_ch1_prop_function_2 (φ : Prop) := fun (X : Prop) => φ X.
```

There are several reasons for such guess. 

First of all, it rhymes with how the hierarchy builds up in chapter 12. For higher order propositions, propositions are those without any real variables; for elementary case, it seems that the only case is when the proposition is just an atomic letter. 

Second, one might compare with definition in [SEP](https://plato.stanford.edu/entries/pm-notation/), that we should distinguish between different letter's meaning: propositions and real variables can have different letter. While there is indeed such a distinction throughout the text, chapter 2, immediately, uses \*1.11 on propositions made up of only `P`, `Q` and `R`, somehow hinting that they are propositional functions, while in ideal case they should be used on `X`, `Y`, `Z` which are exactly the real variables for propositional functions. I believe that the difference of letter is, in this sense, still unclear.

Despite the guess, there are still a lot of places unclear:

With our guess, functions are excluded from identity functions, which means identity function shouldn't appear in our formalization.  By simply searching our formalization we can find that, there is indeed very few appearance of `fun x => x`, but not to nil.

By definition of \*10.01, another severe consequence follows: while chapter 9 still pertains such balance, chapter 10 and onward sets `exists` propositions as *propositional functions*, while `forall` remains to be *propositions*. This unbalance seems very sus.

PM "asserts a function" by asserting a specific value of function, which is, a proposition. So sometimes when asserting a "proposition", it can actually mean "asserting a function". Even still, Russell emphasizes that (p.18):

> It's strictly not asserting a proposition... but practically the same.
