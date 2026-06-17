# Style guide
Note that we might have not cover everything necessary. For things not mentioned in this guide, please refer to the code in chapter 9 - 20 and keep your style as close to them as possible.

## General
Line of code limit: 80 characters as an ideal. In practice, Rocq doesn't come with a native formatter so I cannot do much on this.

Line splitting: line can be splitted either by spaces or by a binary operator, such as
```Rocq
(P ∧ R)
  ∧ Q (* <- Here we split the line *)

(S1
  X Y Z) (* <- Here we split by space *)
```
When splitting by a binary operator, its indentation should indicate the priority, just as propositions rendered by Rocq.

All remaining right brackets `)....)` should be shrinked into one line as much as possible, for example:
```Rocq
pose proof (....(S1
  X Y Z)))...) (* <- We place all right brackets here *)
  as S1.
```

Tabs: all tabs has to be spaces, indented by exactly 2 spaces.

## Naming convention
##### Theorems and propositions
A proposition usually is named with `nxx_yyy`, with `xx_yyy` the number appeared in Principia for that proposition. A few of them are additionally come with their names in the text, and in that case we will adapt the `n` prefix to the name. For example, `Id2_08`. 

Repetitive theorems, for example, if we need to use `Id2_08` twice for separate purposes, we can name them as `Id2_08a` and `Id2_08b` separately. The postfix can continue with  `c`, `d`, ....

##### Parameters
- Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.
- Apparent variables are quantified variables in `∀`, `∃` and so on. As parameters, they're usually lower case literals like `x`.
- Real variables are variables that can directly used in the proofs. They're usually upper case literals like `X`.

##### Variants
One might want to design variants for theorems to provide polymorphism. For *n+2*-order higher version of a theorem `thm`, we name the corresponded theorem `thm_pred_n`; if it's 1-order higher, we name it `thm_pred`. This is actually a bad naming, but I prefer to leave it alone until its necessary.

We might also want to design variants to extend parameter length. For 1 extra parameter, the corresponded `Order` type is `Order2`; one has to manually design `Ordern` if they want to extend beyond. `thm2_pred` should be an example, with a `2` follows immediately after the `thm`, that this variant can accept exactly one more parameter.

When we want to variate over other symbols, for example, from `Prop` to `Class`, the postfix will be changed from `_pred` into `_class`.

And there might exist other variants, designed explicitly in the text, but fall under the same number. For these variants, we postfix with `_alt`, which means alternative, as in `thm_alt`.

##### Variables
**Individuals.** All propositional individuals have to be capital letters like `X`, `Y`, `Z`. 

**Functions.** For function variables being introduced with `Intro_pred`, all of them have to prefixed with `I`, as in `Iφ`. Classes' associated functions are an exception here.

**Quantifiers.** We might sometimes introduce functions as apparent variables, as in `∃ φ`. Here `φ` is mandatory to be typed with `Order n → Prop` to emphasize that it is a typed function.

**Descriptions** A description variable in PM usually looks like `(ιx)(φx)`, with its scope omitted. In our notation, it will be written explicitly with a scope, as the `ιφ` in `[ι φ | ιφ => f ιφ]`. Within the scope, if the function is named `φ`, the corresponded description variable has to be prefixed with `ι`, as in `ιφ`.

**Functions of classes.** These special functions in chapter 20 are introduced with `Intro_pred`, and should be the class name prefixed with `F`, as in `FAlpha` or `Fα`.

**Classes.** Class generally takes the form of `[α @ cα => f cα]`. With in which, we have specific convention on class variables:
- If the function body is given with a function variable `φ`, prefix the name with `c` as in `cφ`
- If the class is being represented with a class variable like `α`, prefix the name in same style, as in `cα`
- If the function is being constructed with a concrete expression like `x ∧ y`, name the var as `c1`, `c2`, ...

In addition, it is worthwhile to note that our current design of class notation could produce false positives: there are cases where it is legal, but disallowed - even we do occur to those disallowed cases in our implementation, due to heavy scoping issues. Here are some cases where you should use *as least as possible*:
- `α ∈ (^ z => ψ z)` where `α` has not be scoped
- `[^z => φ z @ cz1 => cz1 = cz1]` where two `cz1` appears in the same scope. `=` should apply `cz1` separately in two different scopes.
- Expect something like `Intro_class {A : Type} (s : string) : Class.t A.` to directly introduce a class variable into the `TOOLS` section. We should only use classes' functions as variables, for example `Fα`. A class can then be asserted, with `set α := ^z => Fα z`.

**Intro mechanics.** We are mostly using `Intro_pred` and `Intro_individual`. Both of them has a parameter of string. This string parameter is intended to be just a label to indicate what was the variable representing for. It is intended to fill in the variable name with its prefix taken off and its capital case reset. e.g. `X` to `x`, `Fα` to `α`, etc.

**Variants.** There is an exclusive variant for `eq_to_equiv`. All variables should be postfixed with `0` to indicate that we will never use them. e.g. `X` to `X0`, `P` to `P0`, `α` to `α0`. The theorem's names, should be postfixed with `a`, as from `Impl1_01` to `Impl1_01a`. Note that this is a bad naming and conflicts with others, so it is recommended to fix with a better convention.

## Tactics
The general principle is, We want to re-use the names as much as possible, and introduce least extra names as possible. For example:
```Rocq
pose proof (thm0 thm1) as thm0.
destruct S1 as [_ S1].

assert (S2 : ...).
{
  (* proofs... *)
}
assert (S3 : ...).
{
  (* proofs that obtains a `thm0` and `thm1` *)
  Syll_as thm0 thm1 thm0.
  (* `Cn` names are exclusive for conjugated propositions *)
  Conj_as thm0 thm1 C1.
}
```
Other occurrence can be found in the code in chapter 9 - 20.

## Comments
There are several **mandatory** comment pieces:
- `(* simplification *)` is required when you don't want to follow PM's method to prove theorem, and want to introduce "unrelated" Rocq tactics into the context.
- `(* thm ignored *)` is required whenever your proof doesn't use all citations corresponded to the text
- `(* unprovable *)` is required when you have really tried filling in the proof
- `(* UNUSED *)` when you have something unused but feel it necessary to be kept in the codebase

In particular, `destruct` is a common tactic being used in chapter 9 - 20. This should be counted as a `simplification`, although its corresponded theorem should be `Simp`. All simplifications are supposed to be eliminated as much as possible, when we are confident enough to do so.
