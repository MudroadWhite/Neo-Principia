# Appendix B: Propositions, functions and matrices

> The preliminary terror, which chokes off most fifth-form boys from even attempting to learn how to calculate, can be abolished once and for all... That's all.
> 
> \-- *[TO DELIVER YOU FROM THE PRELIMINARY OF TERRORS](https://x.com/JustDeezGuy/status/2062903814621921405)*, random old calculus textbook found on X

----------
Recall what we have described in chapter 1 in [mechanics](./3_mechanics.md/#chapter-1):
- Having something in our proof window means it has been asserted/implied true
- Asserting `H1 : P` means asserting `P` as an **elementary proposition**
- (\*1.1)If there is a rule saying that "if we can assert `H1` then we can assert `H2 : Q`", we are allowed to obtain `H2 : Q` in such a style. It could be happen if we are getting situations like `(|- P) → (|- Q)`(p.92), which doesn't occur within formulae in PM.
- If proposition `X` has been already asserted, `H1 : φ X` is expected to mean asserting an **elementary propositional function**. 
- (\*1.11)If `H2 : φ X → ψ X` can be implied, then we are allowed to imply `H3 : ψ X`.

Observe that `H1 : P` and `H1 : φ X` are essentially the same thing, unless `P` is an individual. For Principia's design, they should be "practically the same"(p.18). Rocq-wise we should actually have 3 ways to represent introducing a function into the context:
1. asserting `H1 : ∀ x, φ x` as Rocq is using `fun x => ...` as the inhabitant of `∀` type. 
2. asserting `H1 : (fun x => ...)` which is impossible, unnecessary and intend to do what `∀` does
3. asserting `H1 : φ X` as in this project, assuming `X` has already been asserted as a proposition.

Although (2) is a very naive attempt, we can still give a closer look. In Rocq, we prove `P` is true if `P` has an inhabitant. The same applies to a function, except that `(fun x => ...)` is only designed to be an inhabitant for `∀` type. For Rocq, we will consider the following examples:

```Rocq

TODO: a theorem of forall, and auto complete it



Theorem TODO

(* Result *)
(* We can see that functions are indeed always the inhabitant for Rocq's `forall` type *)
Check TODO

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

TODO: 
- That being said, we want to make it clear between function type and forall
- such ambiguity also appears when 
    - we want to put a parameter at lhs/rhs
    - Define with `Definition` and with `Axiom`

We want to design the function type
function type is not additionally defined


TODO: matrix


Due to the historical issue that we have to get rid of the "ambiguity" mentioned in the beginning, we are using (3) in the project. (1) should be the correct track: it correctly introduces an inhabitant of a function into the context. It still comes with an apparent fallback: we cannot distinguish when we want to mean it is a function type, and when we want to mean `∀`, so it cannot be used directly.


TODO: reflect with the analysis on functions above; we are inherently always using propositional functions

what if p is asserted, and we assert Phi x? is this safe for function or for prop?
what if p is asserted, and we assert Phi p? is this safe for function or for prop?

TODO: use the example in PO to explain matrix