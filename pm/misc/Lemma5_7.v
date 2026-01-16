Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.

Theorem L5_7 (P Q R S : Prop) :
  ((P↔Q) ∧ (R↔S)) → ((P↔R) → (Q↔S)).
Proof.
  pose (n4_22 Q P R) as n4_22a.
  pose (n4_22 Q R S) as n4_22b.
  pose (Exp3_3 (Q↔R) (R↔S) (Q↔S)) as Exp3_3a.
  MP Exp3_3a n4_22b.
  Syll n4_22a Exp3_3a Sa.
  replace (Q↔P) with (P↔Q) in Sa by
    (apply propositional_extensionality; exact (n4_21 P Q)).
  pose (Imp3_31 ((P↔Q)∧(P↔R)) (R↔S) (Q↔S)) as Imp3_31a.
  MP Imp3_31a Sa.
  replace (((P ↔ Q) ∧ (P ↔ R)) ∧ (R ↔ S)) with 
    ((P ↔ Q) ∧((P ↔ R) ∧ (R ↔ S))) in Imp3_31a.
  2: {
    pose (n4_32 (P <-> Q) (P <-> R) (R <-> S)) as n4_32a.
    apply propositional_extensionality.
    symmetry in n4_32a.
    exact n4_32a.
  }
  replace ((P ↔ R) ∧ (R ↔ S)) with ((R ↔ S) ∧ (P ↔ R)) in Imp3_31a
    by (apply propositional_extensionality; exact (n4_3 (R <-> S) (P <-> R))).
  replace ((P ↔ Q) ∧ (R ↔ S) ∧ (P ↔ R)) with 
    (((P ↔ Q) ∧ (R ↔ S)) ∧ (P ↔ R)) in Imp3_31a
    by (apply propositional_extensionality; exact (n4_32 (P <-> Q) (R <-> S) (P <-> R))).
  pose (Exp3_3 ((P ↔ Q) ∧ (R ↔ S)) (P↔R) (Q↔S)) as Exp3_3b.
  MP Exp3_3b Imp3_31a.
  exact Exp3_3b.
Qed.
