Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.

Theorem N1_4 (P Q : Prop) : P ∨ Q → Q ∨ P.
Proof.
  pose (n2_2 Q P) as n2_2a.
  pose (Assoc1_5 P Q P) as Assoc1_5a.
  pose (Sum1_6 P Q (Q ∨ P)) as Sum1_6a.
  MP Sum1_6a n2_2a.
  Syll Sum1_6a Assoc1_5a Sa.
  pose (Taut1_2 P) as Taut1_2a.
  pose (Sum1_6 Q (P ∨ P) P) as Sum1_6b.
  MP Sum1_6b Taut1_2a.
  Syll Sa Sum1_6b Sb.
  exact Sb.
Qed.
