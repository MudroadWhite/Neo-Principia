Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.

Theorem n3_47a (P Q R S : Prop) : 
  ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof.
  pose (Simp3_26 (P→R) (Q→S)) as Simp3_26a.
  pose (Fact3_45 P R Q) as Fact3_45a.
  Syll Fact3_45a Simp3_26a Sa.
  pose (n3_22 R Q) as n3_22a.
  pose (Syll2_05 (P∧Q) (R∧Q) (Q∧R)) as Syll2_05a. (*Not cited by Jorgensen*)
  MP Syl2_05a n3_22a.
  Syll Sa Syll2_05a Sb.
  pose (Simp3_27 (P→R) (Q→S)) as Simp3_27a.
  pose (Fact3_45 Q S R) as Fact3_45b.
  Syll Simp3_26a Fact3_45b Sc.
  pose (n3_22 S R) as n3_22b.
  pose (Syll2_05 (Q∧R) (S∧R) (R∧S)) as Syll2_05b. (*Not cited by Jorgensen*)
  MP Syl2_05b n3_22b.
  Syll Sc Syll2_05a Sd.
  pose (n2_83 ((P→R)∧(Q→S)) (P∧Q) (Q∧R) (R∧S)) as n2_83a. (*This with MP works, but it omits Conj3_03.*)
  MP n2_83a Sb.
  MP n2_83a Sd.
  exact n2_83a.
Qed.
