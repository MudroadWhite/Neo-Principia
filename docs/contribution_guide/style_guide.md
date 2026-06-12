# Style guide
## General
Line of code limit: 80 characters as an ideal. In practice, Rocq doesn't come with a native formatter so I cannot do much on this.

Line splitting: line can be splitted either by spaces or by a binary operator, such as
```Rocq
(P ∧ R)
∧ Q (* <- Here we split the line *)
```
When splitting by a binary operator, its indentation should indicate the priority, just as propositions rendered by Rocq.

Tabs: all tabs has to be spaces, indented by exactly 2 spaces.

## Naming convention
##### Theorems and propositions
We have naming conventions for propositions. A proposition usually is named with `nxx_yyy`, with `xx_yyy` the number appeared in Principia for that proposition. A few of them are additionally come with their names in the text, and in that case we will adapt the `n` prefix to the name. For example, `Id2_08`. 

##### Parameters
- Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.
- Apparent variables are quantified variables in `∀`, `∃` and so on. As parameters, they're usually lower case literals like `x`.
- Real variables are variables that can directly used in the proofs. They're usually upper case literals like `X`.

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
