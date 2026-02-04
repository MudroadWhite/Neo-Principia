Require Import PM.pm.lib.

(* We first give the axioms of Principia in *1. *)

Theorem Impl1_01 (P Q : Prop) : (P → Q) = (¬ P ∨ Q). 
Proof.
  apply propositional_extensionality.
  split; [ apply imply_to_or | apply or_to_imply ].
Qed.
  (*This is a notational definition in Principia: 
    It is used to switch between "∨" and "→".*)
  
Theorem MP1_1 (P Q : Prop) :
  (P → Q) → P → Q. (*Modus ponens*)
Proof. 
  intros H.
  apply H.
Qed.
  (*1.11 ommitted: it is MP for propositions 
      containing variables. Likewise, ommitted 
      the well-formedness rules 1.7, 1.71, 1.72*)

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

(* Theorem Assoc1_5 : ∀ P Q R : Prop,
  P ∨ (Q ∨ R) → Q ∨ (P ∨ R). (*Association*)
Proof. intros P Q R.
  specialize or_assoc with P Q R.
  intros or_assoc1.
  replace (P ∨ Q ∨ R) with ((P ∨ Q) ∨ R).
  specialize or_comm with P Q.
  intros or_comm1.
  replace (P ∨ Q) with (Q ∨ P).
  specialize or_assoc with Q P R.
  intros or_assoc2.
  replace ((Q ∨ P) ∨ R) with (Q ∨ P ∨ R).
  apply iff_refl.
  apply propositional_extensionality.
  apply iff_sym.
  apply or_assoc2.
  apply propositional_extensionality.
  apply or_comm.
  apply propositional_extensionality.
  apply or_assoc.
Qed. *)

Theorem Sum1_6 (P Q R : Prop) : 
  (Q → R) → (P ∨ Q → P ∨ R). (*Summation*)
Proof. 
  intros QR [HP | HQ].
  { left. apply HP. }
  { right. apply QR in HQ. apply HQ. }
Qed.

(* Theorem Sum1_6 : ∀ P Q R : Prop, 
  (Q → R) → (P ∨ Q → P ∨ R). (*Summation*)
Proof. intros P Q R.
  specialize imply_and_or2 with Q R P.
  intros imply_and_or2a.
  replace (P ∨ Q) with (Q ∨ P).
  replace (P ∨ R) with (R ∨ P).
  apply imply_and_or2a.
  apply propositional_extensionality.
  apply or_comm.
  apply propositional_extensionality.
  apply or_comm.
Qed. *)

(* TODO: redesign MP so that it poses the result as H3
For the current design, sometimes H1 will be changed, while
some other times H2 will be changed. This should be investigated.
Same for the Syll, Conj tactics in later chapters *)
Ltac MP H1 H2 :=
  lazymatch goal with 
    | [ H1 : ?P → ?Q, H2 : ?P |- _ ] => 
      specialize (H1 H2); simpl in H1
  end.
 (*We give this Ltac "MP" to make proofs 
  more human-readable and to more 
  closely mirror Principia's style.*)
