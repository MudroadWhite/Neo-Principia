(* PM.pm.lib - tools, libraries, and others to be used through the project *)

Require Import Unicode.Utf8.
Require Import ClassicalFacts.
Require Import Classical_Prop.
Require Import PropExtensionality.
Require Import String.

Export Unicode.Utf8.
Export Classical_Prop.
Export ClassicalFacts.
Export PropExtensionality.
Export String.

(* cf.p.23: `=` propositions are allowed to be turned into `<->` propositions. An 
alternative tactic to this is `apply propositional_extensionality`. *)
Theorem eq_to_equiv : forall (P Q : Prop),
  (P = Q) -> (P <-> Q).
Proof.
  intros P Q H.
  split; try rewrite -> H; trivial.
Qed.

(* cf.p.51: To instantiate variables appeared in a propositional function, we use 
the concept of "individual", designed as as wrapper just to tag an real variable. 
This allows easy identification on them and they are free to be created everywhere *)
Definition Individual (s : string) : Prop. Admitted.
Example var_0 := Individual "x".

(* cf.p.51: `!` notation *)
(* 
- `!` notation mostly declares the order of a matrix
- matrix is a propositional function totally unquantified
- 1-st order matrix only takes in individuals as its arguments
- 2-st order matrix can take 1-order matrix as its arguments
- any nth-order propositions are supposed to be obtained by generalizing a n-th order matrix

Should we treat `!` as something being denotational just like the dot notations in Principia?
*)
(* Unsatisfying: what we want to express is that Phi takes argument with the same type of `X` *)
(* Here, n is supposed to be the order of the predicate *)
(* Unset Automatic Proposition Inductives. *)
(* Module Predicate.
  Record t {n : nat} : Type := {
    (* This `fix_param` seems to be mostly unused, and might be deleted in the future *)
    fix_param (X : Prop) := fun (f' : Prop -> Prop) => f' X;
    fix_func (f : Prop -> Prop) := fun (X' : Prop) => f X';
  }.
End Predicate. *)
(* Just declares a function is a function of order n *)
Definition Predicate (n : nat) : Type := (Prop -> Prop).
(* Experimental: Similar to `Individual`s, sometimes we need to introduce a predicate(?). Is it unnecessary? *)
Definition Intro_pred (s : string) (n : nat) : Predicate n. Admitted.

(* An alternative version to support functions of 2 arguments *)
(* To be uncommented when the notation is fixed *)
(* Module Predicate2.
  Record t (n : nat) := {
    fix_param (X Y : Prop) := fun (f' : Prop -> Prop -> Prop) => f' X Y;
    fix_func (f : Prop -> Prop -> Prop) := fun (X' Y' : Prop) => f X' Y';
  }.
End Predicate2. *)
(* TODO: maybe we should synthesize these 2 types into one inductive type with the name of "constituent" *)

(* ******** *)
(* AGGREGATED TODOS *)
(* ******** *)
(* TODO:
Add scope for each of the chapter, on definitions of `~` and `\/`, since they are supposed to be only work on "one type of propositions"
Should we also add scope for `MP` and `Syll`?
Design a `comma` predicate  which works like a `id` `to enforce "lazy evaluation" on quantifiers 
*)

(* ******** *)
(* NOTES *)
(* ******** *)
(* 
https://lawrencecpaulson.github.io/2025/10/15/Proofs-trivial.html
https://plato.stanford.edu/entries/pm-notation/
https://en.wikipedia.org/wiki/Glossary_of_Principia_Mathematica
https://randall-holmes.github.io/Drafts/notesonpm.pdf
https://www.religion-online.org/article/the-axiomatic-matrix-of-whiteheads-process-and-reality/
https://nap.nationalacademies.org/read/10866/chapter/66

~p.14:
- propositional function: the functions that we usually concern, like `Phi` `Psi` etc..

~p.17:
- descriptive funstion: a special kind of propositional function, including examples like `x is blue`
- `~` is not a primitive idea. It is supposed to have a different definition on different types of proposition. 
For example, we might define `~` a typeclass, and `forall` propositions has an instance of implementation for 
this operator

~p.18:
apparent variable "appears to be" the only variables, while "real variables" include the actual variants to be concluded

~p.20: 
- (Ax, Px -> Q x) -> (Ax, Px) -> (Ax, Qx) requires that P Q takes arguments "of the same type". -> p.49
- formal implication: the `->` wrapped up in `forall`s. It bypassed the problem that `P -> Q = ~P \/ Q`, and restrict that we have to 
know `forall x, P x -> Q x` and `P X` to get `Q X`.

~p.22:
(TODO)`=` is not defined until chapter 13, and this is being explained in chapter 2/chapter II.

~p.40:
- a nice counterexample to test a function P is well typed is to see if `P P` can be formed
- `P P` is also an example that `P` is *impossible* to be a value of `P`
- P with "all possible values" are called `significant`. Significant = "well typed"

~p.47, beginning of chapter II:
- `forall x, Phi x` is considered as a function with `Phi` as one argument
- for `forall`, `Phi` can be a parameter but an individual `X` cannot be a parameter
- it is necesssary to make a distinction between passing in a `X` and passing in a `Phi`

~p.49:
- We can construct a function taking 2 arguments, and return either a function of function or a function of individual. 
It turns out that the return type is untyped. To enforce the return type with a fixed type, we have to enforce arguments
of a function taking the same type

~p.50:
- A propositional function could possibly contain apparent variables. We can eliminate apparent variables 
  and source them back to real variables
- matrix: A function made up of no apparent variable, to generate a "matrix" of elementary propositions

~p.51:
- predicate: first order functions. Only takes individuals as parameters
- Phi ! x^: any Phi that is a first order function/predicate and takes an variable of `x`'s type
- Phi ! x: `Phi ! x^` instantiated by `x`
- `Phi ! x^` could be the type of a real variable which is not an individual
- "Individual" is the best thing to instantiate a function's parameters
- (TODO)They are designed to be not propositions. Why?
- (TODO)Why we have to design the hierarchy for "functions" and "propositions " separately?

~p.52:
- `!` notation also seems to be used only when the function is being considered as a variable(at rhs)? And for all other cases, they are 
  supposed to be fixed(at rhs)?
- `!`'s summary: this is not a notation just for first order functions, but it's more like a notation for function being identified as 
  a variable at rhs

~p.56:
- the axiom of reducibility: "any" properties should have a equivalent of itself in a collection of properties

~p.57:
- exaplained a proof of identity `=` informally, only to be complete with the support of axiom of reducibility

~p.94:
- (notes on *1.01)the rules for definitional equality is out of the theory

~p.127:
- Chapter II has explained that ~ and \/ should have different meaning on different propositions. Guess: we cannot define a
negation on "all" propositions attributing to Russell's paradox

~p.128:
- Goal of ch9: focus on definition of `~` and `\/` defined in *1 - *5 limited to eprops. Extend their definitions to 1st orde props
- The support of `forall` and `exists` seems to be only for demonstration purpose - if we take them as primitive ideas, we can 
  conclude "upgraded" versions of propositions "just as in" ch1-5.
- the important parts seems to be *1.2 - *1.6; A new way is used for analogue of 1.7 - 1.72
- Real variables doesn't have types(??), and can be instantiated with any proposition of any orders???
- Summary:
  - elementary propositions are initially admitted, along with their types
  - definition of `~` and `\/` depends on proposition types
  - definition of function depends on type of `~` and `\/`
  - order of a proposition depends on its parameter's types

~p.138:
- Ch9 enables us to take `forall` propositions as parameters
- therefore we can have a better goal(?)
- Goal of ch10: focus on deducing 1-var functions from 
- "for example", `exists` is no longer a primitive idea which is different from ch9  
- several ch9 theorems are only taken because of their ability to reason for quantified propositions

~p.162:
- (TODO) propositions is defined in p.43. They are supposed to be incomplete symbols, but individuals are complete 
  so they are not propositions
- matrix is predicative function as a definition
- starting from chapter 12, all variables are either matrixes or individuals
- propositions being used as variables(??) will no longer be used
*)
