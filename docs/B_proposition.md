# Appendix B: Propositions, functions and matrices

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

----------
Recall what we have described in chapter 1 in [mechanics](./3_mechanics.md/#chapter-1):
> - Having something in our proof window means it has been asserted/implied true
> - Asserting `H1 : P` means asserting `P` as an **elementary proposition**
> - (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) → (|- Q)`(p.92), which doesn't occur within formulae in PM.
> - If proposition `X` has been already asserted, `H1 : φ X` is expected to mean asserting an **elementary propositional function**. 
> - (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.

Observe that `H1 : P` and `H1 : φ X` are essentially the same thing, unless `P` is an individual. For Principia's design, they should be "practically the same"(p.18). But let's check how should these type be understood in Rocq's default. We have the following options to represent the assertion of a function:
1. `H1 : ∀ x, φ x` as Rocq is using `fun x => ...` as the inhabitant of `∀` type
2. `H1 : (fun x => ...)` which is impossible, unnecessary and intend to do what (1) does
3. `H1 : φ X` as in this project, assuming `X` has already been asserted as a proposition

Although (2) is a very naive attempt, we can still give a closer look. In Rocq, we prove `P` is true if `P` has an inhabitant; `H1 : P` means `P` as a type being presented, has an inhabitant. The same should apply to a function, except that 
- `(fun x => ...)` is designed to be an inhabitant for `∀`, and never a type on its own
- `→` is a special case for `∀`, thus `(fun x => ...)` could also be an legal inhabitant of `→`
- Under CH correspondence, `→` is also used as the type for a function
Where none of these connections has been assumed in PM.

To assert function *inhabited*, we need to design a proper type to represent the functions and get it *inhabited*, as something like `Function X (expression...)`... turns out to be our option (1) which is Rocq's `∀`. However, `∀` turns out to be such a fundamental type that it is the most direct representation to the prototype of dependent product type, `Π` or `Prod` in OCaml's impementation to Rocq(TODO: link, reference).

TODO: 
- Vernacs
  - lhs & rhs
  - intrepretation to `Definition`s and `Axiom`s
- Summary
  - our current design of soft embedding is inherently using \*1.11 by the analysis above; to make it clearer, for \*1.1 we should have (TODO: to explore with example snippets)
  - Our project doesn't design a proper function type, but should be a feature in the future
- Corner cases
  - what if p is asserted, and we assert Phi x? is this safe for function or for prop?
  - what if p is asserted, and we assert Phi p? is this safe for function or for prop?



```Rocq
Definition example_1 := (fun (P : Prop) => P).
Check example_1.
(* fun P : Prop => P
    : Prop → Prop *)

Definition example_2 (P : Prop) : P.
Proof. Admitted. 
Check example_2.
(* ∀ P : Prop, P *)

(*

fun (P : Prop) => 
    fun (H : P) => H
        : forall P : Prop, P -> P

*)

(* Vernac `Definition` is completely the same as `Theorem` to use with *)
Definition TODO
Definition TODO: failed attempt

(* Vernac `Axiom` has a slight difference comparing to the two above *)
Axiom TODO
Axiom TODO: failed attempt

(* Result *)
Check (Theorem)

(* Result in the goal window *)
pose proof TODO: definition
```

For chapter 12 and beyond, we are having a completely different interpretation for what are propositions and what are functions. We demonstrate the difference by the example given in this [PhilOverflow Q&A](TODO):

```Rocq
TODO: 
Suppose we have a function `f1 := (fun x y => x /\ y)` and another function `f2 := (fun p q -> p \/ q)`, and we want to substitute the `x` in `f1` with `p \/ q`. By Russell's idea, we shall be allowed to construct the application form as `f1 f2` and the result of the application should be `f1 f2 = (fun p q y => (p \/ q) /\ y)`. We can immediately see that lambda calculus seems like a tedious design for such abstraction; and Russell designs the representation for functions just exactly like propositions. The result shall be `(X /\ Y) (P \/ Q) = ((P \/ Q) /\ Y)` if we are clear that `X` is to substituted by `f2`.

```


1. (p.162)Matrix is a function with arbitrary length of variables, but without any apparent variables("For the sake of clearness...")
2. (p.164)PM's hierarchy comes to design so that *variables in the hierarchies are either individuals or matrices*("A function is said to be predicative when it is a matrix..."). Which means
    1. Matrices can be applied, or apply onto matrices, just like functions
    2. At the same time, matrices can be asserted, just like propositions
    3. On the other hand, the definition of propositions has become narrower to "propositions" with all variables quantified
3. (p.164)"Propositions, which have occurred hitherto as variables, will no longer do so except in a few isolated cases of which no subsequent use is made."
