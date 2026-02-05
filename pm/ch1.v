Require Import PM.pm.lib.

(* We first give the axioms of Principia in *1. *)

Theorem Impl1_01 (P Q : Prop) : (P → Q) = (¬ P ∨ Q). 
Proof.
  apply propositional_extensionality.
  split; [ apply imply_to_or | apply or_to_imply ].
Qed.
(* This is a notational definition in Principia: 
  It is used to switch between "∨" and "→". *)
  
(* Pp. 1.1: Anything implied by a true elementary proposition is true *)
(* Although being written down informally, designing an ltac to pick the 
  right and asserted hypothesis and produce a new hypothesis, is exactly what
  Principia wants to do. Since it will be used very frequently we omit the 
  number for this Ltac *)
Ltac MP H1 H2 :=
  lazymatch goal with 
    | [ H1 : ?P → ?Q, H2 : ?P |- _ ] => 
      pose proof (H1 H2) as H1; simpl in H1
  end.

(* *1.11 ommitted: it is MP for propositions containing variables. *)

Theorem Taut1_2 (P : Prop) :
  P ∨ P → P. (*Tautology*)
Proof. 
  apply imply_and_or.
  apply iff_refl.
Qed.

Theorem Add1_3 (P Q : Prop) :
  Q → P ∨ Q. (*Addition*)
Proof. 
  apply or_intror.
Qed.

Theorem Perm1_4 (P Q : Prop) :
  P ∨ Q → Q ∨ P. (*Permutation*)
Proof. 
  apply or_comm.
Qed.

(* Reference: https://softwarefoundations.cis.upenn.edu/lf-current/Logic.html#or_assoc *)
Theorem Assoc1_5 (P Q R : Prop) :
  P ∨ (Q ∨ R) → Q ∨ (P ∨ R).
Proof.
  intros [H | [H | H]].
  { right. left. apply H. }
  { left. apply H. }
  { right. right. apply H. }
Qed.


Theorem Sum1_6 (P Q R : Prop) : 
  (Q → R) → (P ∨ Q → P ∨ R). (*Summation*)
Proof. 
  intros QR [HP | HQ].
  { left. apply HP. }
  { right. apply QR in HQ. apply HQ. }
Qed.
