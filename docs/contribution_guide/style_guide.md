# Style guide
## General
Line of code limit: 80 characters as an ideal. In practice, Rocq doesn't come with a native formatter so I cannot do much on this.

Line splitting: line can be splitted either by spaces or by a binary operator, such as
```Rocq
(P /\ R)
/\ Q (* <- Here we split the line *)
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
**Functions of classes.** These special functions in chapter 20 are introduced with `Intro_pred`, and should be the class name prefixed with `F`, as in `FAlpha` or `Fα`.
- Descriptions: A description variable in PM usually looks like `(ιx)(φx)`, with its scope omitted. In our notation, it will be written explicitly with a scope, as the `ιφ` in `[ι φ | ιφ => f ιφ]` where `f` is a function.
- More to be added...

for class variables:
- If the function body is given with a function variable Phi, name the var as cPhi
- If the function is being constructed in more detail, name the var as c1, c2, ...
- If the class is being represented with a class variable, name the variable exactly
  the same as the class var

for introduced variables:
- implicit `Phi` predicates should be introduced as `IPhi`
- class instance should be introduced as `Alpha` (so far)

representation which turns out to be illegal(which our notation design 
doesn't prevent) :
- X ∈ (^ z => Psi z)
- [^z => Phi z @ cz1 => cz1 = cz1]
- Definition Intro_class {A : Type} (s : string) : Class.t A. Admitted.

TODO: for function variables of `forall`/`exists`, `Order n` is mandatory