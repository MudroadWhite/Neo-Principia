Require Import PM.pm.lib.
Require Import PM.pm.ch10.
Require Import PM.pm.ch11.

Open Scope formal_equiv.

(* 
NOTE:

- `F` for AoR is having a level of exactly 1
- constants in PM can be designed as a tagged label them just as constants when passing as a parameter
into rocq
*)

(* Is it that we have designed `n12_1` totally wrong..? *)
Definition n12_1 (φ : Prop → Prop) : 
  ∃ f : (Order 1), (φ x) <[- x -]> ((fun (F : Order 1) =>
    F x) f).
Admitted.

Module Experimental.
  (*
  (* For untyped function, it seems that it has to be something like `A -> B` 
  where `x : A` and the rest of the arguments are being put into `B` *)
  Definition n12_1_alt {A B : Type} (φ : A -> B) :
    ∃ f : (Order 1), (φ x) <[- x -]> f x.
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
  (* Definition fix_param (n : nat) (X : Prop) := fun (F : Order n) => F X. *)

  (* Definition e12_1 (n : nat) (s : string) (Phi : Prop → Prop) (X : Prop) :
    let f := Intro_pred s n in
    (Phi = f) ∧ (Phi X ↔ (fix_param n X) f).
  Admitted. *)
End Experimental.

(* To be uncommented *)
(* Definition n12_11 (f Phi : Prop → Prop → Prop) :
  ∃ fPsi : Prop → Prop → Prop,
    ∃ f : Order2.t 1, (Phi x y) <[- x y -]> (f.(Order2.fix_func 1) x y fPsi).
Admitted. *)

Close Scope formal_equiv.
