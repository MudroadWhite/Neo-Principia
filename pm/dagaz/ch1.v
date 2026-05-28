Require Import PM.pm.lib.

(* We first give the axioms of Principia in *1. *)

Theorem Impl1_01 (P Q : Prop) : (P → Q) = (¬ P ∨ Q). 
Admitted.
(* This is a notational definition in Principia: 
  It is used to switch between "∨" and "→". *)
  
(* Pp. 1.1: Anything implied by a true elementary proposition is true *)

(* Pp. 1.11: Modus ponens *)
(* Although being written down informally, designing an ltac to pick the 
  right and asserted hypothesis and produce a new hypothesis, is exactly what
  Principia wants to do. Since it will be used very frequently we omit the 
  number for this Ltac *)
Ltac MP H1 H2 :=
  match goal with 
  | [ _H1 : ?P → ?Q |- _ ] => 
    constr_eq H1 _H1;
    pose proof (H1 H2) as H1; 
    simpl in H1
  end.

Ltac MP_debug H1 H2 D1 D2 :=
  match goal with 
  | [ _H1 : ?P → ?Q |- _ ] => 
    constr_eq H1 _H1;
    assert (D1 : P) by admit
  end.

Theorem Taut1_2 (P : Prop) :
  P ∨ P → P. (*Tautology*)
Admitted.

Theorem Add1_3 (P Q : Prop) :
  Q → P ∨ Q. (*Addition*)
Admitted.

Theorem Perm1_4 (P Q : Prop) :
  P ∨ Q → Q ∨ P. (*Permutation*)
Admitted.

(* Reference: https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html#or_assoc *)
Theorem Assoc1_5 (P Q R : Prop) :
  P ∨ (Q ∨ R) → Q ∨ (P ∨ R).
Admitted.

Theorem Sum1_6 (P Q R : Prop) : 
  (Q → R) → (P ∨ Q → P ∨ R). (*Summation*)
Admitted.
