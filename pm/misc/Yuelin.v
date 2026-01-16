Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.

Theorem n3_47 (P Q R S : Prop) : ((P → R) ∧ (Q → S)) → (P ∧ Q) → R ∧ S.
Proof.
  assert (Sa : (P → R) ∧ (Q → S) → P ∧ Q → Q ∧ R).
  {
    pose (Simp3_26 (P→R) (Q→S)) as Simp3_26a. (*Yuelin's book has n2_34. This doesn't exist.*) 
    pose (Fact3_45 P R Q) as Fact3_45a. (*Yuelin's book has n2_45. Fact3_45 is meant.*)
    replace (R∧Q) with (Q∧R) in Fact3_45a
      by (apply propositional_extensionality; exact (n4_3 Q R)).
    Syll Simp3_26a Fact3_45a Sa. (*Syll2_05*)
    exact Sa.
  }
  assert (Sb : (P → R) ∧ (Q → S) → Q ∧ R → R ∧ S).
  {
    pose (Simp3_27 (P→R) (Q→S)) as Simp3_27a. (*Yuelin's book has n2_36. This doesn't exist.*)
    pose (Fact3_45 Q S R) as Fact3_45b. (*Yuelin's book has n2_45. Fact3_45 is meant.*)
    replace (S∧R) with (R∧S) in Fact3_45b
      by (apply propositional_extensionality; exact (n4_3 R S)).
    Syll Simp3_27a Fact3_45b Sb. (*Syll2_05*)
    exact Sb.
  }
  Conj Sa Sb H.
  pose (Comp3_43 ((P→R)∧(Q→S)) ((P∧Q)→(Q∧R)) ((Q∧R)→(R∧S))) as Comp3_43a. (*Yuelin's book has n2_39. Comp3_43 is meant. PM and I have n2_83 here.*)
  MP Comp3_43a H.
  pose (Syll3_33 (P∧Q) (Q∧R) (R∧S)) as Syll3_33a. (*Yuelin's book has n2_39. Syll3_33 is meant. My n2_83 does this work, too.*)
  Syll Comp3_43a Syll3_33a Sc. (*Yuelin seems to do another application of Syll3_33, citing the same number n2_39. But that would also require here, as above, Conjunction, which Yuelin does not bother citing.*)
  exact Sc.
Qed.
