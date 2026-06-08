# Style guide

## General
- Line of code limit: 80 characters as an ideal. In practice, Rocq doesn't come with a native formatter so I cannot do much on this.
- TODO: Splitting a line by binop; indentation: no tab, only space x2;

## Naming convention

TODO: rewrite all below

**Theorems and propositions.** 
We have naming conventions for propositions. A proposition usually is named with `nxx_yyy`, with `xx_yyy` the number appeared in Principia for that proposition. A few of them are additionally come with their names in the text, and in that case we will adapt the `n` prefix to the name. For example, `Id2_08`. 

Now we come to naming conventions for (lhs) parameters.
- Functions as parameters are supposed to be named as the same style of original text: either greek letters like `φ` or their upper-cased English equivalent like `Phi`.
- Apparent variables are quantified variables in `∀`, `∃` and so on. As parameters, they're usually lower case literals like `x`.
- Real variables are variables that can directly used in the proofs. They're usually upper case literals like `X`.

**Variables.** 
(there are different kinds of variables... some from notations)

- Individuals: Sometimes, functions might be introduced on purpose as *individuals* of higher order. These individuals are prefixed with `I` as in `Iφ`. For individual of order 0(just a proposition), although it is in the same naming convention as real variables, we're planning to use things like `IX` in the future to maintain a clear distinction.
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
