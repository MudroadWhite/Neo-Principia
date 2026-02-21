Require Import PM.pm.lib.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

Open Scope formal_equiv.

(* 
Starting from chapter 12, every variables being quantified at the rhs has to be
either an "Individual" or a "Predicate". For example, "∀ P, P ∧ Q" might 
never appear, and instead, it will be either "∀ Individual P, P ∧ Q" or 
"∀ Predicate Phi, Phi (Individual P)" where Phi P = P ∧ Q

Ideally speaking, AoR is the only way to convert "function"s in a theorem to 
"predicate"s. But the representation here has been very annoying. The `∀`
here has been working differently to `Phi x` and `f x`: `x` is a parameter for
`Phi` but it is fixed for `f`, and `f` is actually the "parameter".
*)

(* 
NOTE:

cf.p.162: In this chapter, Phi!x^ is given an exact meaning where `x^` is an individual 
and `Phi` is a function taking an individual as argument

`F` for AoR is having a level of exactly 1

cf.p.163: a function is either a matrix itself or a generalization on a matrix. Therefore 
functions in PM has a very different meaning from what people will acknowledge nowadays, 
and matrix seems more like the actual `function`

cf.p.163&164: `(x).Phi!x` is a function with argument `x`, while `(Phi).Phi!x` is 
a function with argument `Phi`. This makes the ambiguity of `!` very clear: it only 
states that `Phi` must be a predicative function but doesn't ensure that it is taken 
as a parameter...

More on `!` notation: when it is not being used, `Phi` is pretty much untyped. when it 
is being used, the type level has to be directly obtained by how many levels of `!`s are 
being used(cf.p.162, definition of a 1st-order predicative)

more..: cf.p.162, bottom part: new def of function arises from both using apparent 
variables/real variables as variables. matrix contains only variables that needs to be 
fed in by Rocq; propositions contains only quantified variables that are self sufficient

cf.p.163: first order propositions: regardless of the count of `forall` and `exists`, highest 
level of argument is always level 0

cf.p.164, bottom: in previous chapter, propositions can be taken as variables?

cf.p.165: order is different from type?

cf.p.165, example of 2nd-order function: individual can be a parameter of any level higher order 
function...which we didn't characterize so far. Can we design a type for that?

it seems that our def of `Predicate` needs a renewal soon, to define `A -> B` correctly

NOTE: for constants we can design a tagto label them just as constants when passing as a parameter
into rocq
*)

(* Is it that we have designed `n12_1` totally wrong..? *)
Definition n12_1 (φ : Prop → Prop) : 
  ∃ f : (Predicate 1), (φ x) <[- x -]> ((fun (F : Predicate 1) =>
    F x) f).
Admitted.

Module Experimental.
  (*
  (* For untyped function, it seems that it has to be something like `A -> B` 
  where `x : A` and the rest of the arguments are being put into `B` *)
  Definition n12_1_alt {A B : Type} (φ : A -> B) :
    ∃ f : (Predicate 1), (φ x) <[- x -]> f x.
  Admitted.
  *)

  (* 
  To actually use it, I think there should be some other better way to express
  especially for our current formalization. This might be able to be done exactly 
  because we are using shallow embedding, and the operators are additionally subject 
  to interpretation in Rocq... 
  While it might not actually do it successfully, this theorem is supposed to help
  generating the predicative versions of the theorems.
  This implementation, however, suffers another drawback: it is not the same 
  literal representation as in original text. For example it doesn't have the 
  `∀` as in original text, but the `∀` in Principia, as we can see, 
  works differently on functions and predicates.
  Currently I believe that AoR in this chapter is more likely a rule to write and understand
  the older theorems in another way (see `_pred`-suffixed theorems in later chapter)
  and it shouldn't be written in formula
  *)
  (* Definition fix_param (n : nat) (X : Prop) := fun (F : Predicate n) => F X. *)

  (* Definition e12_1 (n : nat) (s : string) (Phi : Prop → Prop) (X : Prop) :
    let f := Intro_pred s n in
    (Phi = f) ∧ (Phi X ↔ (fix_param n X) f).
  Admitted. *)
End Experimental.

(* To be uncommented *)
(* Definition n12_11 (f Phi : Prop → Prop → Prop) :
  ∃ fPsi : Prop → Prop → Prop,
    ∃ f : Predicate2.t 1, (Phi x y) <[- x y -]> (f.(Predicate2.fix_func 1) x y fPsi).
Admitted. *)

Close Scope formal_equiv.
