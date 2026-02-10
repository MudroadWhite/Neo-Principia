Require Import PM.pm.lib.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

Open Scope single_formal_equiv.
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

Definition n12_1 (n : nat) (φ : Prop → Prop) : 
  ∃ f : (Predicate n), (φ x) <[- x -]> ((fun (F : Predicate n) =>
    F x) f).
Admitted.

Module Experimental.
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
  Definition fix_param (n : nat) (X : Prop) := fun (F : Predicate n) => F X.

  Definition e12_1 (n : nat) (s : string) (Phi : Prop → Prop) (X : Prop) :
    let f := Intro_pred s n in
    (Phi = f) ∧ (Phi X ↔ (fix_param n X) f).
  Admitted.
End Experimental.

(* To be uncommented *)
(* Definition n12_11 (f Phi : Prop → Prop → Prop) :
  ∃ fPsi : Prop → Prop → Prop,
    ∃ f : Predicate2.t 1, (Phi x y) <[- x y -]> (f.(Predicate2.fix_func 1) x y fPsi).
Admitted. *)

Close Scope single_formal_equiv.
Close Scope formal_equiv.
