Require Import PM.pm.lib.
Require Import PM.pm.ch1.
Require Import PM.pm.ch2.
Require Import PM.pm.ch3.
Require Import PM.pm.ch4.

Theorem n5_1 (P Q : Prop) :
  (P ∧ Q) → (P ↔ Q).
Proof.
  pose proof (n3_4 P Q) as n3_4a.
  pose proof (n3_4 Q P) as n3_4b.
  pose proof (n3_22 P Q) as n3_22a.
  Syll n3_22a n3_4b Sa.
  clear n3_22a. clear n3_4b.
  Conj n3_4a Sa C.
  pose proof (n4_76 (P ∧ Q) (P → Q) (Q → P)) as n4_76a. (*Not cited*)
  apply propositional_extensionality in n4_76a.
  symmetry in n4_76a.
  replace ((P ∧ Q → P → Q) ∧ (P ∧ Q → Q → P)) with 
      (P ∧ Q → (P → Q) ∧ (Q → P)) in C 
      by now apply n4_76a.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in C
    by now rewrite Equiv4_01.
  exact C.
Qed. 

Theorem n5_11 (P Q : Prop) :
  (P → Q) ∨ (¬ P → Q).
Proof.
  pose proof (n2_5 P Q) as n2_5a.
  pose proof (n2_54 (P → Q) (¬ P → Q)) as n2_54a.
  MP n2_54a n2_5a.
  exact n2_54a.
Qed.
  (*The proof sketch cites n2_51, 
      but this may be a misprint.*)

Theorem n5_12 (P Q : Prop) :
  (P → Q) ∨ (P → ¬ Q).
Proof.
  pose proof (n2_51 P Q) as n2_51a.
  pose proof (n2_54 ((P → Q)) (P → ¬ Q)) as n2_54a.
  MP n2_54a n2_5a.
  exact n2_54a.
Qed.
  (*The proof sketch cites n2_52, 
      but this may be a misprint.*)

Theorem n5_13 (P Q : Prop) :
  (P → Q) ∨ (Q → P).
Proof.
  pose proof (n2_521 P Q) as n2_521a.
  replace (¬ (P → Q) → Q → P) with 
      (¬¬ (P → Q) ∨ (Q → P)) in n2_521a
      by now rewrite <- Impl1_01.
  pose proof (n4_13 (P → Q)) as n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (P → Q)) with (P → Q)
    in n2_521a by now apply n4_13a.
  exact n2_521a.
Qed. 

Theorem n5_14 (P Q R : Prop) :
  (P → Q) ∨ (Q → R).
Proof.
  pose proof (Simp2_02 P Q) as Simp2_02a.
  pose proof (Transp2_16 Q (P → Q)) as Transp2_16a.
  MP Transp2_16a Simp2_02a.
  pose proof (n2_21 Q R) as n2_21a.
  Syll Transp2_16a n2_21a Sa.
  replace (¬ (P → Q) → (Q → R)) with 
      (¬¬ (P → Q) ∨ (Q → R)) in Sa
      by now rewrite <- Impl1_01.
  pose proof (n4_13 (P → Q)) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (P → Q)) with (P → Q) in Sa
    by now apply n4_13a.
  exact Sa.
Qed.

Theorem n5_15 (P Q : Prop) :
  (P ↔ Q) ∨ (P ↔ ¬ Q).
Proof.
  pose proof (n4_61 P Q) as n4_61a.
  replace (¬ (P → Q) ↔ P ∧ ¬ Q) with 
      ((¬ (P → Q) → P ∧ ¬ Q) ∧ ((P ∧ ¬ Q) → ¬ (P → Q))) in n4_61a
      by now rewrite Equiv4_01.
  pose proof (Simp3_26 (¬ (P → Q) → P ∧ ¬ Q) 
    ((P ∧ ¬ Q) → ¬ (P → Q))) as Simp3_26a.
  MP Simp3_26a n4_61a.
  pose proof (n5_1 P (¬ Q)) as n5_1a.
  Syll Simp3_26a n5_1a Sa.
  pose proof (n2_54 (P → Q) (P ↔ ¬ Q)) as n2_54a.
  MP n2_54a Sa.
  pose proof (n4_61 Q P) as n4_61b.
  replace ((¬ (Q → P)) ↔ (Q ∧ ¬ P)) with 
      (((¬ (Q → P)) → (Q ∧ ¬ P)) ∧ ((Q ∧ ¬ P) → (¬ (Q → P)))) 
      in n4_61b by now rewrite Equiv4_01.
  pose proof (Simp3_26 
      (¬ (Q → P) → (Q ∧ ¬ P)) ((Q ∧ ¬ P) → (¬ (Q → P)))) as Simp3_26b.
  MP Simp3_26b n4_61b.
  pose proof (n5_1 Q (¬ P)) as n5_1b.
  Syll Simp3_26b n5_1b Sb.
  pose proof (n4_12 P Q) as n4_12a.
  apply propositional_extensionality in n4_12a.
  replace (Q ↔ ¬ P) with (P ↔ ¬ Q) in Sb 
    by now apply n4_12a.
  pose proof (n2_54 (Q → P) (P ↔ ¬ Q)) as n2_54b.
  MP n2_54b Sb.
  replace (¬ (P → Q) → P ↔ ¬ Q) with 
      (¬¬ (P → Q) ∨ (P ↔ ¬ Q)) in Sa
      by now rewrite <- Impl1_01.
  pose proof (n4_13 (P → Q)) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (P → Q)) with (P → Q) in Sa
    by now apply n4_13a.
  replace (¬ (Q → P) → (P ↔ ¬ Q)) with 
      (¬¬ (Q → P) ∨ (P ↔ ¬ Q)) in Sb
      by now rewrite <- Impl1_01.
  pose proof (n4_13 (Q → P)) as n4_13b.
  apply propositional_extensionality in n4_13b.
  replace (¬¬ (Q → P)) with (Q → P) in Sb
    by now apply n4_13b.
  clear n4_61a. clear Simp3_26a. clear n5_1a. 
      clear n2_54a. clear n4_61b. clear Simp3_26b. 
      clear n5_1b. clear n4_12a. clear n2_54b.
      clear n4_13a. clear n4_13b.
  Conj Sa Sb C.
  pose proof (n4_31 (P → Q) (P ↔ ¬ Q)) as n4_31a.
  apply propositional_extensionality in n4_31a.
  symmetry in n4_31a.
  replace ((P → Q) ∨ (P ↔ ¬ Q)) with 
      ((P ↔ ¬ Q) ∨ (P → Q)) in C
      by now apply n4_31a.
  pose proof (n4_31 (Q → P) (P ↔ ¬ Q)) as n4_31b.
  apply propositional_extensionality in n4_31b.
  symmetry in n4_31b.
  replace ((Q → P) ∨ (P ↔ ¬ Q)) with 
      ((P ↔ ¬ Q) ∨ (Q → P)) in C
      by now apply n4_31b.
  pose proof (n4_41 (P ↔ ¬ Q) (P → Q) (Q → P)) as n4_41a.
  apply propositional_extensionality in n4_41a.
  replace (((P ↔ ¬ Q) ∨ (P → Q)) ∧ ((P ↔ ¬ Q) ∨ (Q → P))) 
      with ((P ↔ ¬ Q) ∨ (P → Q) ∧ (Q → P)) in C
      by now apply n4_41a.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in C
    by now rewrite Equiv4_01.
  pose proof (n4_31 (P ↔ ¬ Q) (P ↔ Q)) as n4_31c.
  apply propositional_extensionality in n4_31c.
  symmetry in n4_31c.
  replace ((P ↔ ¬ Q) ∨ (P ↔ Q)) with 
      ((P ↔ Q) ∨ (P ↔ ¬ Q)) in C
      by now apply n4_31c.
  exact C.
Qed.

Theorem n5_16 (P Q : Prop) :
  ¬ ((P ↔ Q) ∧ (P ↔ ¬ Q)).
Proof.
  pose proof (Simp3_26 ((P → Q) ∧ (P → ¬ Q)) (Q → P)) as Simp3_26a.
  pose proof (Id2_08 ((P ↔ Q) ∧ (P → ¬ Q))) as Id2_08a.
  pose proof (n4_32 (P → Q) (P → ¬ Q) (Q → P)) as n4_32a.
  apply propositional_extensionality in n4_32a.
  symmetry in n4_32a.
  replace (((P → Q) ∧ (P → ¬ Q)) ∧ (Q → P)) with 
      ((P → Q) ∧ ((P → ¬ Q) ∧ (Q → P))) in Simp3_26a
      by now apply n4_32a.
  pose proof (n4_3 (Q → P) (P → ¬ Q)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((P → ¬ Q) ∧ (Q → P)) with 
      ((Q → P) ∧ (P → ¬ Q)) in Simp3_26a
      by now apply n4_3a.
  pose proof (n4_32 (P → Q) (Q → P) (P → ¬ Q)) as n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((P → Q) ∧ (Q → P) ∧ (P → ¬ Q)) with 
      (((P → Q) ∧ (Q → P)) ∧ (P → ¬ Q)) in Simp3_26a
      by now apply n4_32b.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q)
       in Simp3_26a by now rewrite Equiv4_01.
  Syll Id2_08a Simp3_26a Sa.
  pose proof (n4_82 P Q) as n4_82a.
  apply propositional_extensionality in n4_82a.
  symmetry in n4_82a.
  replace ((P → Q) ∧ (P → ¬ Q)) with (¬ P) in Sa
    by now apply n4_82a.
  pose proof (Simp3_27 
      (P → Q) ((Q → P) ∧ (P → ¬ Q))) as Simp3_27a.
  replace ((P → Q) ∧ (Q → P) ∧ (P → ¬ Q)) with 
      (((P → Q) ∧ (Q → P)) ∧ (P → ¬ Q)) in Simp3_27a
      by now apply n4_32b.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
      in Simp3_27a by now rewrite Equiv4_01.
  pose proof (Syll3_33 Q P (¬ Q)) as Syll3_33a.
  Syll Simp3_27a Syll2_06a Sb.
  pose proof (Abs2_01 Q) as Abs2_01a.
  Syll Sb Abs2_01a Sc.
  clear Sb. clear Simp3_26a. clear Id2_08a. 
      clear n4_82a. clear Simp3_27a. clear Syll3_33a. 
      clear Abs2_01a. clear n4_32a. clear n4_32b. clear n4_3a.
  Conj Sa Sc C.
  pose proof (Comp3_43 ((P ↔ Q) ∧ (P → ¬ Q)) (¬ P) (¬ Q)) as Comp3_43a.
  MP Comp3_43a C.
  pose proof (n4_65 Q P) as n4_65a.
  pose proof (n4_3 (¬ P) (¬ Q)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (¬ Q ∧ ¬ P) with (¬ P ∧ ¬ Q) in n4_65a
    by now apply n4_3a.
  apply propositional_extensionality in n4_65a.
  replace (¬ P ∧ ¬ Q) with (¬ (¬ Q → P)) in Comp3_43a
    by now apply n4_65a.
  pose proof (Exp3_3 (P ↔ Q) (P → ¬ Q) (¬ (¬ Q → P))) as Exp3_3a.
  MP Exp3_3a Comp3_43a.
  replace ((P → ¬ Q) → ¬ (¬ Q → P)) with 
      (¬ (P → ¬ Q) ∨ ¬ (¬ Q → P)) in Exp3_3a
      by now rewrite <- Impl1_01.
  pose proof (n4_51 (P → ¬ Q) (¬ Q → P)) as n4_51a.
  apply propositional_extensionality in n4_51a.
  replace (¬ (P → ¬ Q) ∨ ¬ (¬ Q → P)) with 
      (¬ ((P → ¬ Q) ∧ (¬ Q → P))) in Exp3_3a
      by now apply n4_51a.
  replace ((P → ¬ Q) ∧ (¬ Q → P)) with (P ↔ ¬ Q) 
    in Exp3_3a by now rewrite Equiv4_01.
  replace ((P ↔ Q) → ¬ (P ↔ ¬ Q)) with 
      (¬ (P ↔ Q) ∨ ¬ (P ↔ ¬ Q)) in Exp3_3a
      by now rewrite Impl1_01.
  pose proof (n4_51 (P ↔ Q) (P ↔ ¬ Q)) as n4_51b.
  apply propositional_extensionality in n4_51b.
  replace (¬ (P ↔ Q) ∨ ¬ (P ↔ ¬ Q)) with 
      (¬ ((P ↔ Q) ∧ (P ↔ ¬ Q))) in Exp3_3a
      by now apply n4_51b.
  exact Exp3_3a.
Qed.

Theorem n5_17 (P Q : Prop) :
  ((P ∨ Q) ∧ ¬ (P ∧ Q)) ↔ (P ↔ ¬ Q).
Proof.
  pose proof (n4_64 Q P) as n4_64a.
  pose proof (n4_21 (Q ∨ P) (¬ Q → P)) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((¬ Q → P) ↔ (Q ∨ P)) with 
      ((Q ∨ P) ↔ (¬ Q → P)) in n4_64a
      by now apply n4_21a.
  pose proof (n4_31 P Q) as n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n4_64a
    by now apply n4_31a.
  pose proof (n4_63 P Q) as n4_63a.
  pose proof (n4_21 (P ∧ Q) (¬ (P → ¬ Q))) as n4_21b.
  apply propositional_extensionality in n4_21b.
  replace (¬ (P → ¬ Q) ↔ P ∧ Q) with 
      (P ∧ Q ↔ ¬ (P → ¬ Q)) in n4_63a
      by now apply n4_21b.
  pose proof (Transp4_11 (P ∧ Q) (¬ (P → ¬ Q))) as Transp4_11a.
  pose proof (n4_13 (P → ¬ Q)) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (P → ¬ Q)) with (P → ¬ Q) 
    in Transp4_11a by now apply n4_13a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace (P ∧ Q ↔ ¬ (P → ¬ Q)) with 
      (¬ (P ∧ Q) ↔ (P → ¬ Q)) in n4_63a
      by now apply Transp4_11a.
  clear Transp4_11a. clear n4_21a.
  clear n4_31a. clear n4_21b. clear n4_13a.
  Conj n4_64a n4_63a C.
  pose proof (n4_38 (P ∨ Q) (¬ (P ∧ Q)) (¬ Q → P) (P → ¬ Q)) as n4_38a.
  MP n4_38a C.
  replace ((¬ Q → P) ∧ (P → ¬ Q)) with (¬ Q ↔ P)
       in n4_38a by now rewrite Equiv4_01.
  pose proof (n4_21 P (¬ Q)) as n4_21c.
  apply propositional_extensionality in n4_21c.
  replace (¬ Q ↔ P) with (P ↔ ¬ Q) in n4_38a
    by now apply n4_21c.
  exact n4_38a.
Qed.

Theorem n5_18 (P Q : Prop) :
  (P ↔ Q) ↔ ¬ (P ↔ ¬ Q).
Proof.
  pose proof (n5_15 P Q) as n5_15a.
  pose proof (n5_16 P Q) as n5_16a.
  Conj n5_15a n5_16a C.
  pose proof (n5_17 (P ↔ Q) (P ↔ ¬ Q)) as n5_17a.
  rewrite Equiv4_01 in n5_17a.
  pose proof (Simp3_26 
    ((((P ↔ Q) ∨ (P ↔ ¬ Q)) ∧ ¬ ((P ↔ Q) ∧ (P ↔ ¬ Q)))
    → ((P ↔ Q) ↔ ¬ (P ↔ ¬ Q))) (((P ↔ Q) ↔ ¬ (P ↔ ¬ Q)) → 
    (((P ↔ Q) ∨ (P ↔ ¬ Q)) ∧ ¬ ((P ↔ Q) ∧ (P ↔ ¬ Q))))) as Simp3_26a. (*not cited*)
  MP Simp3_26a n5_17a.
  MP Simp3_26a C.
  exact Simp3_26a.
Qed.

Theorem n5_19 (P : Prop) :
  ¬ (P ↔ ¬ P).
Proof.
  pose proof (n5_18 P P) as n5_18a.
  pose proof (n4_2 P) as n4_2a.
  rewrite Equiv4_01 in n5_18a.
  pose proof (Simp3_26 (P ↔ P → ¬ (P ↔ ¬ P))
    (¬ (P ↔ ¬ P) → P ↔ P)) as Simp3_26a. (*not cited*)
  MP Simp3_26a n5_18a.
  MP Simp3_26a n4_2a.
  exact Simp3_26a.
Qed.

Theorem n5_21 (P Q : Prop) :
  (¬ P ∧ ¬ Q) → (P ↔ Q).
Proof.
  pose proof (n5_1 (¬ P) (¬ Q)) as n5_1a.
  pose proof (Transp4_11 P Q) as Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  replace (¬ P ↔ ¬ Q) with (P ↔ Q) in n5_1a
    by now apply Transp4_11a.
  exact n5_1a.
Qed.

Theorem n5_22 (P Q : Prop) :
  ¬ (P ↔ Q) ↔ ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)).
Proof.
  pose proof (n4_61 P Q) as n4_61a.
  pose proof (n4_61 Q P) as n4_61b.
  Conj n4_61a n4_61b C.
  pose proof (n4_39 (¬ (P → Q)) (¬ (Q → P)) (P ∧ ¬ Q) (Q ∧ ¬ P)) as n4_39a.
  MP n4_39a C.
  pose proof (n4_51 (P → Q) (Q → P)) as n4_51a.
  apply propositional_extensionality in n4_51a.
  replace (¬ (P → Q) ∨ ¬ (Q → P)) with 
      (¬ ((P → Q) ∧ (Q → P))) in n4_39a
      by now apply n4_51a.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) 
      in n4_39a by now rewrite Equiv4_01.
  exact n4_39a.
Qed.

Theorem n5_23 (P Q : Prop) :
  (P ↔ Q) ↔ ((P ∧ Q) ∨ (¬ P ∧ ¬ Q)).
Proof.
  pose proof (n5_18 P Q) as n5_18a.
  pose proof (n5_22 P (¬ Q)) as n5_22a.
  Conj n5_18a n5_22a C.
  pose proof (n4_22 (P ↔ Q) (¬ (P ↔ ¬ Q)) 
    (P ∧ ¬¬ Q ∨ ¬ Q ∧ ¬ P)) as n4_22a.
  MP n4_22a C.
  pose proof (n4_13 Q) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ Q) with Q in n4_22a by now apply n4_13a.
  pose proof (n4_3 (¬ P) (¬ Q)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (¬ Q ∧ ¬ P) with (¬ P ∧ ¬ Q) in n4_22a
    by now apply n4_3a.
  exact n4_22a.
Qed. 
  (*The proof sketch in Principia offers n4_36. 
    This seems to be a misprint. We used n4_3.*)

Theorem n5_24 (P Q : Prop) :
  ¬ ((P ∧ Q) ∨ (¬ P ∧ ¬ Q)) ↔ ((P ∧ ¬ Q) ∨ (Q ∧ ¬ P)).
Proof.
  pose proof (n5_23 P Q) as n5_23a.
  pose proof (Transp4_11 (P ↔ Q) 
    (P ∧ Q ∨ ¬ P ∧ ¬ Q)) as Transp4_11a. (*Not cited*)
  rewrite Equiv4_01 in Transp4_11a.
  pose proof (Simp3_26 (((P ↔ Q) ↔ P ∧ Q ∨ ¬ P ∧ ¬ Q)
    → (¬ (P ↔ Q) ↔ ¬ (P ∧ Q ∨ ¬ P ∧ ¬ Q))) 
    ((¬ (P ↔ Q) ↔ ¬ (P ∧ Q ∨ ¬ P ∧ ¬ Q))
    → ((P ↔ Q) ↔ P ∧ Q ∨ ¬ P ∧ ¬ Q))
  ) as Simp3_26a.
  MP Simp3_26a Transp4_11a.
  MP Simp3_26a n5_23a.
  pose proof (n5_22 P Q) as n5_22a.
    clear n5_23a. clear Transp4_11a.
  Conj Simp3_26a n5_22a C.
  pose proof (n4_22 (¬ (P ∧ Q ∨ ¬ P ∧ ¬ Q))
    (¬ (P ↔ Q)) (P ∧ ¬ Q ∨ Q ∧ ¬ P)) as n4_22a.
  pose proof (n4_21 (¬ (P ∧ Q ∨ ¬ P ∧ ¬ Q)) (¬ (P ↔ Q))) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((¬ (P ↔ Q)) ↔ (¬ ((P ∧ Q) ∨ (¬ P ∧ ¬ Q))))
    with ((¬ ((P ∧ Q) ∨ (¬ P ∧ ¬ Q))) ↔ (¬ (P ↔ Q))) in C
    by now apply n4_21a.
  MP n4_22a C.
  exact n4_22a.
Qed. 

Theorem n5_25 (P Q : Prop) :
  (P ∨ Q) ↔ ((P → Q) → Q).
Proof.
  pose proof (n2_62 P Q) as n2_62a.
  pose proof (n2_68 P Q) as n2_68a.
  Conj n2_62a n2_68a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_3 (P Q R : Prop) :
  ((P ∧ Q) → R) ↔ ((P ∧ Q) → (P ∧ R)).
Proof.
  pose proof (Comp3_43 (P ∧ Q) P R) as Comp3_43a.
  pose proof (Exp3_3 (P ∧ Q → P) 
    (P ∧ Q → R) (P ∧ Q → P ∧ R)) as Exp3_3a. (*Not cited*)
  MP Exp3_3a Comp3_43a.
  pose proof (Simp3_26 P Q) as Simp3_26a.
  MP Exp3_3a Simp3_26a.
  pose proof (Syll2_05 (P ∧ Q) (P ∧ R) R) as Syll2_05a.
  pose proof (Simp3_27 P R) as Simp3_27a.
  MP Syll2_05a Simp3_27a.
  clear Comp3_43a. clear Simp3_27a. 
      clear Simp3_26a.
  Conj Exp3_3a Syll2_05a C.
  Equiv C.
  exact C.
Qed. 

Theorem n5_31 (P Q R : Prop) :
  (R ∧ (P → Q)) → (P → (Q ∧ R)).
Proof.
  pose proof (Comp3_43 P Q R) as Comp3_43a.
  pose proof (Simp2_02 P R) as Simp2_02a.
  pose proof (Exp3_3 
      (P → R) (P → Q) (P → (Q ∧ R))) as Exp3_3a. (*Not cited*)
  pose proof (n3_22 (P → R) (P → Q)) as n3_22a. (*Not cited*)
  Syll n3_22a Comp3_43a Sa.
  MP Exp3_3a Sa.
  Syll Simp2_02a Exp3_3a Sb.
  pose proof (Imp3_31 R (P → Q) (P → (Q ∧ R))) as Imp3_31a. (*Not cited*)
  MP Imp3_31a Sb.
  exact Imp3_31a.
Qed. 

Theorem n5_32 (P Q R : Prop) :
  (P → (Q ↔ R)) ↔ ((P ∧ Q) ↔ (P ∧ R)).
Proof.
  pose proof (n4_76 P (Q → R) (R → Q)) as n4_76a.
  pose proof (Exp3_3 P Q R) as Exp3_3a.
  pose proof (Imp3_31 P Q R) as Imp3_31a.
  Conj Exp3_3a Imp3_31a Ca.
  Equiv Ca.
  pose proof (Exp3_3 P R Q) as Exp3_3b.
  pose proof (Imp3_31 P R Q) as Imp3_31b.
  Conj Exp3_3b Imp3_31b Cb.
  Equiv Cb.
  pose proof (n5_3 P Q R) as n5_3a.
  pose proof (n5_3 P R Q) as n5_3b.
  apply propositional_extensionality in Ca.
  replace (P → Q → R) with (P ∧ Q → R) in n4_76a
    by now apply Ca.
  apply propositional_extensionality in Cb.
  replace (P → R → Q) with (P ∧ R → Q) in n4_76a
    by now apply Cb.
  apply propositional_extensionality in n5_3a.
  symmetry in n5_3a.
  replace (P ∧ Q → R) with (P ∧ Q → P ∧ R) in n4_76a
    by now apply n5_3a.
  apply propositional_extensionality in n5_3b.
  symmetry in n5_3b.
  replace (P ∧ R → Q) with (P ∧ R → P ∧ Q) in n4_76a
    by now apply n5_3b.
  replace ((P ∧ Q → P ∧ R) ∧ (P ∧ R → P ∧ Q)) with 
      ((P ∧ Q) ↔ (P ∧ R)) in n4_76a 
      by now rewrite Equiv4_01.
  pose proof (n4_21 (P → ((Q → R) ∧ (R → Q))) ((P ∧ Q) ↔ (P ∧ R))) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace ((P ∧ Q ↔ P ∧ R) ↔ (P → (Q → R) ∧ (R → Q))) with 
      ((P → (Q → R) ∧ (R → Q)) ↔ (P ∧ Q ↔ P ∧ R)) in n4_76a
      by now apply n4_21a.
  replace ((Q → R) ∧ (R → Q)) with (Q ↔ R) in n4_76a
    by now rewrite Equiv4_01.
  exact n4_76a.
Qed.

Theorem n5_33 (P Q R : Prop) :
  (P ∧ (Q → R)) ↔ (P ∧ ((P ∧ Q) → R)).
Proof.
  pose proof (n5_32 P (Q → R) ((P ∧ Q) → R)) as n5_32a.
  replace 
      ((P → (Q → R) ↔ (P ∧ Q → R)) ↔ (P ∧ (Q → R) ↔ P ∧ (P ∧ Q → R))) 
      with 
      (((P → (Q → R) ↔ (P ∧ Q → R)) → (P ∧ (Q → R) ↔ P ∧ (P ∧ Q → R)))
      ∧
      ((P ∧ (Q → R) ↔ P ∧ (P ∧ Q → R) → (P → (Q → R) ↔ (P ∧ Q → R))))) 
      in n5_32a by now rewrite Equiv4_01.
  pose proof (Simp3_26  
      ((P → (Q → R) ↔ (P ∧ Q → R)) → (P ∧ (Q → R) ↔ P ∧ (P ∧ Q → R))) 
      ((P ∧ (Q → R) ↔ P ∧ (P ∧ Q → R) → (P → (Q → R) ↔ (P ∧ Q → R))))) as Simp3_26a. (*Not cited*)
  MP Simp3_26a n5_32a.
  pose proof (n4_73 Q P) as n4_73a.
  pose proof (n4_84 Q (Q ∧ P) R) as n4_84a.
  Syll n4_73a n4_84a Sa.
  pose proof (n4_3 P Q) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace (Q ∧ P) with (P ∧ Q) in Sa 
    by now apply n4_3a. (*Not cited*)
  MP Simp3_26a Sa.
  exact Simp3_26a.
Qed.

Theorem n5_35 (P Q R : Prop) :
  ((P → Q) ∧ (P → R)) → (P → (Q ↔ R)).
Proof.
  pose proof (Comp3_43 P Q R) as Comp3_43a.
  pose proof (n5_1 Q R) as n5_1a.
  pose proof (Syll2_05 P (Q ∧ R) (Q ↔ R)) as Syll2_05a.
  MP Syll2_05a n5_1a.
  Syll Comp3_43a Syll2_05a Sa.
  exact Sa.
Qed.

Theorem n5_36 (P Q : Prop) :
  (P ∧ (P ↔ Q)) ↔ (Q ∧ (P ↔ Q)).
Proof.
  pose proof (Id2_08 (P ↔ Q)) as Id2_08a.
  pose proof (n5_32 (P ↔ Q) P Q) as n5_32a.
  apply propositional_extensionality in n5_32a.
  symmetry in n5_32a.
  replace (P ↔ Q → P ↔ Q) with 
      ((P ↔ Q) ∧ P ↔ (P ↔ Q) ∧ Q) in Id2_08a
      by now apply n5_32a.
  pose proof (n4_3 P (P ↔ Q)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((P ↔ Q) ∧ P) with (P ∧ (P ↔ Q)) in Id2_08a
    by now apply n4_3a.
  pose proof (n4_3 Q (P ↔ Q)) as n4_3b.
  apply propositional_extensionality in n4_3b.
  replace ((P ↔ Q) ∧ Q) with (Q ∧ (P ↔ Q)) in Id2_08a
    by now apply n4_3b.
  exact Id2_08a.
Qed. 
  (*The proof sketch cites Ass3_35 and n4_38, 
    but the sketch was indecipherable.*)

Theorem n5_4 (P Q : Prop) :
  (P → (P → Q)) ↔ (P → Q).
Proof.
  pose proof (n2_43 P Q) as n2_43a.
  pose proof (Simp2_02 (P) (P → Q)) as Simp2_02a.
  Conj n2_43a Simp2_02a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_41 (P Q R : Prop) :
  ((P → Q) → (P → R)) ↔ (P → Q → R).
Proof.
  pose proof (n2_86 P Q R) as n2_86a.
  pose proof (n2_77 P Q R) as n2_77a.
  Conj n2_86a n2_77a C.
  Equiv C.
  exact C.
Qed.

Theorem n5_42 (P Q R : Prop) :
  (P → Q → R) ↔ (P → Q → P ∧ R).
Proof.
  pose proof (n5_3 P Q R) as n5_3a.
  pose proof (Imp3_31 P Q R) as Imp3_31a.
  pose proof (Exp3_3 P Q R) as Exp3_3a.
  Conj Imp3_31a Exp3_3 Ca.
  Equiv Ca.
  apply propositional_extensionality in Ca.
  replace ((P ∧ Q) → R) with (P → Q → R) in n5_3a
    by now apply Ca.
  pose proof (Imp3_31 P Q (P ∧ R)) as Imp3_31b.
  pose proof (Exp3_3 P Q (P ∧ R)) as Exp3_3b.
  Conj Imp3_31b Exp3_3b Cb.
  Equiv Cb.
  apply propositional_extensionality in Cb.
  replace ((P ∧ Q) → (P ∧ R)) with 
      (P → Q → (P ∧ R)) in n5_3a by now apply Cb.
  exact n5_3a.
Qed. 

Theorem n5_44 (P Q R : Prop) :
  (P → Q) → ((P → R) ↔ (P → (Q ∧ R))).
Proof.
  pose proof (n4_76 P Q R) as n4_76a.
  rewrite Equiv4_01 in n4_76a.
  pose proof (Simp3_26 
    (((P → Q) ∧ (P → R)) → (P → (Q ∧ R)))
    ((P → (Q ∧ R)) → ((P → Q) ∧ (P → R)))) as Simp3_26a.
  MP Simp3_26a n4_76a.
  pose proof (Simp3_27
    (((P → Q) ∧ (P → R)) → (P → (Q ∧ R)))
    ((P → (Q ∧ R)) → ((P → Q) ∧ (P → R)))) as Simp3_27a.
  MP Simp3_27a n4_76a.
  pose proof (Simp3_27 (P → Q) (P → Q ∧ R)) as Simp3_27d.
  Syll Simp3_27d Simp3_27a Sa.
  pose proof (n5_3 (P → Q) (P → R) (P → (Q ∧ R))) as n5_3a.
  rewrite Equiv4_01 in n5_3a.
  pose proof (Simp3_26 
    ((((P → Q) ∧ (P → R)) → (P → (Q ∧ R))) → 
    (((P → Q) ∧ (P → R)) → ((P → Q) ∧ (P → (Q ∧ R)))))
    ((((P → Q) ∧ (P → R)) → ((P → Q) ∧ (P → (Q ∧ R))))
    → (((P → Q) ∧ (P → R)) → (P → (Q ∧ R))))) as Simp3_26b.
  MP Simp3_26b n5_3a.
  pose proof (Simp3_27 
  ((((P → Q) ∧ (P → R)) → (P → (Q ∧ R))) → 
  (((P → Q) ∧ (P → R)) → ((P → Q) ∧ (P → (Q ∧ R)))))
  ((((P → Q) ∧ (P → R)) → ((P → Q) ∧ (P → (Q ∧ R))))
  → (((P → Q) ∧ (P → R)) → (P → (Q ∧ R))))) as Simp3_27b.
  MP Simp3_27b n5_3a.
  MP Simp3_26a Simp3_26b.
  MP Simp3_27a Simp3_27b.
  clear n4_76a. clear Simp3_26a. clear Simp3_27a. 
    clear Simp3_27b. clear Simp3_27d. clear n5_3a.
  Conj Simp3_26b Sa C.
  Equiv C.
  pose proof (n5_32 (P → Q) (P → R) (P → (Q ∧ R))) as n5_32a.
  rewrite Equiv4_01 in n5_32a.
  pose proof (Simp3_27 
    (((P → Q) → (P → R) ↔ (P → Q ∧ R))
      → (P → Q) ∧ (P → R) ↔ (P → Q) ∧ (P → Q ∧ R))
    ((P → Q) ∧ (P → R) ↔ (P → Q) ∧ (P → Q ∧ R)
      → (P → Q) → (P → R) ↔ (P → Q ∧ R))) as Simp3_27c.
  MP Simp3_27c n5_32a.
  pose proof (n4_21 
    ((P → Q) ∧ (P → R)) ((P → Q) ∧ (P → (Q ∧ R)))) as n4_21a.
  apply propositional_extensionality in n4_21a.
  replace (((P → Q) ∧ (P → (Q ∧ R))) ↔ ((P → Q) ∧ (P → R)))
    with (((P → Q) ∧ (P → R)) ↔ ((P → Q) ∧ (P → (Q ∧ R))))
    in C by now apply n4_21a.
  MP Simp3_27c C.
  exact Simp3_27c.
Qed. 

Theorem n5_5 (P Q : Prop) :
  P → ((P → Q) ↔ Q).
Proof.
  pose proof (Ass3_35 P Q) as Ass3_35a.
  pose proof (Exp3_3 P (P → Q) Q) as Exp3_3a.
  MP Exp3_3a Ass3_35a.
  pose proof (Simp2_02 P Q) as Simp2_02a.
  pose proof (Exp3_3 P Q (P → Q)) as Exp3_3b.
  pose proof (n3_42 P Q (P → Q)) as n3_42a. (*Not cited*)
  MP n3_42a Simp2_02a.
  MP Exp3_3b n3_42a.
  clear n3_42a. clear Simp2_02a. clear Ass3_35a.
  Conj Exp3_3a Exp3_3b C.
  pose proof (n3_47 P P ((P → Q) → Q) (Q → (P → Q))) as n3_47a.
  MP n3_47a C.
  pose proof (n4_24 P) as n4_24a. (*Not cited*)
  apply propositional_extensionality in n4_24a.
  replace (P ∧ P) with P in n3_47a by now apply n4_24a. 
  replace (((P → Q) → Q) ∧ (Q → (P → Q))) with ((P → Q) ↔ Q)
    in n3_47a by now rewrite Equiv4_01.
  exact n3_47a.
Qed.

Theorem n5_501 (P Q : Prop) :
  P → (Q ↔ (P ↔ Q)).
Proof.
  pose proof (n5_1 P Q) as n5_1a.
  pose proof (Exp3_3 P Q (P ↔ Q)) as Exp3_3a.
  MP Exp3_3a n5_1a.
  pose proof (Ass3_35 P Q) as Ass3_35a.
  pose proof (Simp3_26 (P ∧ (P → Q)) (Q → P)) as Simp3_26a. (*Not cited*)
  Syll Simp3_26a Ass3_35a Sa.
  pose proof (n4_32 P (P → Q) (Q → P)) as n4_32a. (*Not cited*)
  apply propositional_extensionality in n4_32a.
  symmetry in n4_32a.
  replace ((P ∧ (P → Q)) ∧ (Q → P)) with 
      (P ∧ ((P → Q) ∧ (Q → P))) in Sa by now apply n4_32a.
  replace ((P → Q) ∧ (Q → P)) with (P ↔ Q) in Sa
    by now rewrite Equiv4_01.
  pose proof (Exp3_3 P (P ↔ Q) Q) as Exp3_3b.
  MP Exp3_3b Sa.
  clear n5_1a. clear Ass3_35a. clear n4_32a.
      clear Simp3_26a. clear Sa. 
  Conj Exp3_3a Exp3_3b C.
  pose proof (n4_76 P (Q → (P ↔ Q)) ((P ↔ Q) → Q)) as n4_76a. (*Not cited*)
  apply propositional_extensionality in n4_76a.
  symmetry in n4_76a.
  replace ((P → Q → P ↔ Q) ∧ (P → P ↔ Q → Q)) with 
      ((P → (Q → P ↔ Q) ∧ (P ↔ Q → Q))) in C
      by now apply n4_76a.
  replace ((Q → (P ↔ Q)) ∧ ((P ↔ Q) → Q)) with 
      (Q ↔ (P ↔ Q)) in C by now rewrite Equiv4_01.
  exact C.
Qed.

Theorem n5_53 (P Q R S : Prop) :
  (((P ∨ Q) ∨ R) → S) ↔ (((P → S) ∧ (Q → S)) ∧ (R → S)).
Proof.
  pose proof (n4_77 S (P ∨ Q) R) as n4_77a.
  pose proof (n4_77 S P Q) as n4_77b.
  apply propositional_extensionality in n4_77b.
  replace (P ∨ Q → S) with 
      ((P → S) ∧ (Q → S)) in n4_77a
      by now apply n4_77b. (*Not cited*)
  pose proof (n4_21 ((P ∨ Q) ∨ R → S) 
      (((P → S) ∧ (Q → S)) ∧ (R → S))) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace ((((P → S) ∧ (Q → S)) ∧ (R → S)) ↔ (((P ∨ Q) ∨ R) → S)) 
      with 
      ((((P ∨ Q) ∨ R) → S) ↔ (((P → S) ∧ (Q → S)) ∧ (R → S))) 
      in n4_77a by now apply n4_21a.
  exact n4_77a.
Qed.

Theorem n5_54 (P Q : Prop) :
  ((P ∧ Q) ↔ P) ∨ ((P ∧ Q) ↔ Q).
Proof.
  pose proof (n4_73 P Q) as n4_73a.
  pose proof (n4_44 Q P) as n4_44a.
  pose proof (Transp2_16 Q (P ↔ (P ∧ Q))) as Transp2_16a.
  MP n4_73a Transp2_16a.
  pose proof (n4_3 P Q) as n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q ∧ P) with (P ∧ Q) in n4_44a
    by now apply n4_3a.
  pose proof (Transp4_11 Q (Q ∨ (P ∧ Q))) as Transp4_11a.
  apply propositional_extensionality in Transp4_11a.
  symmetry in Transp4_11a.
  replace (Q ↔ Q ∨ P ∧ Q) with 
      (¬ Q ↔ ¬ (Q ∨ P ∧ Q)) in n4_44a by now apply Transp4_11a.
  apply propositional_extensionality in n4_44a.
  symmetry in n4_44a.
  replace (¬ Q) with (¬ (Q ∨ P ∧ Q)) in Transp2_16a
    by now apply n4_44a.
  pose proof (n4_56 Q (P ∧ Q)) as n4_56a. (*Not cited*)
  apply propositional_extensionality in n4_56a.
  replace (¬ (Q ∨ P ∧ Q)) with 
      (¬ Q ∧ ¬ (P ∧ Q)) in Transp2_16a
      by now apply n4_56a.
  pose proof (n5_1 (¬ Q) (¬ (P ∧ Q))) as n5_1a.
  Syll Transp2_16a n5_1a Sa.
  replace (¬ (P ↔ P ∧ Q) → (¬ Q ↔ ¬ (P ∧ Q))) with 
      (¬¬ (P ↔ P ∧ Q) ∨ (¬ Q ↔ ¬ (P ∧ Q))) in Sa
      by now rewrite Impl1_01. (*Not cited*)
  pose proof (n4_13 (P ↔ (P ∧ Q))) as n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (P ↔ P ∧ Q)) with (P ↔ P ∧ Q) in Sa
    by now apply n4_13a.
  pose proof (Transp4_11 Q (P ∧ Q)) as Transp4_11b.
  apply propositional_extensionality in Transp4_11b.
  replace (¬ Q ↔ ¬ (P ∧ Q)) with (Q ↔ (P ∧ Q)) in Sa
    by now apply Transp4_11b.
  pose proof (n4_21 (P ∧ Q) Q) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (Q ↔ (P ∧ Q)) with ((P ∧ Q) ↔ Q) in Sa
    by now apply n4_21a.
  pose proof (n4_21 (P ∧ Q) P) as n4_21b. (*Not cited*)
  apply propositional_extensionality in n4_21b.
  replace (P ↔ (P ∧ Q)) with ((P ∧ Q) ↔ P) in Sa
    by now apply n4_21b.
  exact Sa.
Qed. 

Theorem n5_55 (P Q : Prop) :
  ((P ∨ Q) ↔ P) ∨ ((P ∨ Q) ↔ Q).
Proof.
  pose proof (Add1_3 (P ∧ Q) (P)) as Add1_3a.
  pose proof (n4_3 P Q) as n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  pose proof (n4_41 P Q P) as n4_41a. (*Not cited*)
  replace (Q ∧ P) with (P ∧ Q) in n4_41a 
    by now apply n4_3a.
  pose proof (n4_31 (P ∧ Q) P) as n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (P ∨ P ∧ Q) with (P ∧ Q ∨ P) in n4_41a
    by now apply n4_31a.
  apply propositional_extensionality in n4_41a.
  symmetry in n4_41a.
  replace ((P ∧ Q) ∨ P) with ((P ∨ Q) ∧ (P ∨ P)) in Add1_3a
    by now apply n4_41a.
  pose proof (n4_25 P) as n4_25a. (*Not cited*)
  apply propositional_extensionality in n4_25a.
  replace (P ∨ P) with P in Add1_3a
    by now apply n4_25a.
  pose proof (n4_31 P Q) as n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (Q ∨ P) with (P ∨ Q) in Add1_3a
    by now apply n4_31b. 
  pose proof (n5_1 P (P ∨ Q)) as n5_1a.
  pose proof (n4_3 (P ∨ Q) P) as n4_3b.
  apply propositional_extensionality in n4_3b.
  symmetry in n4_3b.
  replace ((P ∨ Q) ∧ P) with (P ∧ (P ∨ Q)) in Add1_3a
    by now apply n4_3b.
  Syll Add1_3a n5_1a Sa.
  pose proof (n4_74 P Q) as n4_74a.
  pose proof (Transp2_15 P (Q ↔ P ∨ Q)) as Transp2_15a. (*Not cited*)
  MP Transp2_15a n4_74a.
  Syll Transp2_15a Sa Sb.
  replace (¬ (Q ↔ P ∨ Q) → P ↔ P ∨ Q) with
    (¬¬ (Q ↔ P ∨ Q) ∨ (P ↔ P ∨ Q)) in Sb 
    by now rewrite Impl1_01.
  pose proof (n4_13 (Q ↔ P ∨ Q)) as n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬ (Q ↔ (P ∨ Q))) with (Q ↔ (P ∨ Q)) in Sb
    by now apply n4_13a.
  pose proof (n4_21 (P ∨ Q) Q) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (Q ↔ (P ∨ Q)) with ((P ∨ Q) ↔ Q) in Sb
    by now apply n4_21a.
  pose proof (n4_21 (P ∨ Q) P) as n4_21b. (*Not cited*)
  apply propositional_extensionality in n4_21b.
  replace (P ↔ (P ∨ Q)) with ((P ∨ Q) ↔ P) in Sb
    by now apply n4_21b.
  apply n4_31 in Sb.
  exact Sb. 
Qed.

Theorem n5_6 (P Q R : Prop) :
  ((P ∧ ¬ Q) → R) ↔ (P → (Q ∨ R)).
Proof.
  
  pose proof (n4_87 P (¬ Q) R) as n4_87.
  (* For simplicity... we will just destruct the branch that we want
  to apply in the following proof. Originally this involves `Simp` *)
  destruct n4_87 as [n4_87a n4_87r]. clear n4_87r.
  assert (S1 : (P ∧ ¬ Q → R) → (P → Q ∨ R)).
  {
    destruct n4_87a as [n4_87al n4_87ar]. clear n4_87ar.
    pose proof (n4_64 Q R) as n4_64.
    pose proof (n4_85 (¬ Q → R) (Q ∨ R) P) as n4_85.
    MP n4_85 n4_64.
    now rewrite -> n4_85 in n4_87al.
  }
  assert (S2 : (P → Q ∨ R) → (P ∧ ¬ Q → R)).
  {
    destruct n4_87a as [n4_87al n4_87ar]. clear n4_87al.
    pose proof (n4_64 Q R) as n4_64.
    pose proof (n4_85 (¬ Q → R) (Q ∨ R) P) as n4_85.
    MP n4_85 n4_64.
    now rewrite -> n4_85 in n4_87ar.
  }
  Conj S1 S2 C1.
  now Equiv C1.
Qed.

Theorem n5_61 (P Q : Prop) :
  ((P ∨ Q) ∧ ¬ Q) ↔ (P ∧ ¬ Q).
Proof.
  pose proof (n4_74 Q P) as n4_74a.
  pose proof (n5_32 (¬ Q) P (Q ∨ P)) as n5_32a.
  apply propositional_extensionality in n5_32a.
  symmetry in n5_32a.
  replace (¬ Q → P ↔ Q ∨ P) with 
      (¬ Q ∧ P ↔ ¬ Q ∧ (Q ∨ P)) in n4_74a
      by now apply n5_32a.
  pose proof (n4_3 P (¬ Q)) as n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (¬ Q ∧ P) with (P ∧ ¬ Q) in n4_74a
    by now apply n4_3a.
  pose proof (n4_3 (Q ∨ P) (¬ Q)) as n4_3b. (*Not cited*)
  apply propositional_extensionality in n4_3b.
  replace (¬ Q ∧ (Q ∨ P)) with ((Q ∨ P) ∧ ¬ Q) in n4_74a
    by now apply n4_3b.
  pose proof (n4_31 P Q) as n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n4_74a
    by now apply n4_31a.
  pose proof (n4_21 ((P ∨ Q) ∧ ¬ Q) (P ∧ ¬ Q)) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∧ ¬ Q ↔ (P ∨ Q) ∧ ¬ Q) with 
      ((P ∨ Q) ∧ ¬ Q ↔ P ∧ ¬ Q) in n4_74a
      by now apply n4_21a.
  exact n4_74a.
Qed.

Theorem n5_62 (P Q : Prop) :
  ((P ∧ Q) ∨ ¬ Q) ↔ (P ∨ ¬ Q).
Proof.
  pose proof (n4_7 Q P) as n4_7a.
  replace (Q → P) with (¬ Q ∨ P) in n4_7a
    by now rewrite Impl1_01.
  replace (Q → (Q ∧ P)) with (¬ Q ∨ (Q ∧ P)) in n4_7a
    by now rewrite Impl1_01.
  pose proof (n4_31 (Q ∧ P) (¬ Q)) as n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (¬ Q ∨ (Q ∧ P)) with ((Q ∧ P) ∨ ¬ Q) in n4_7a
    by now apply n4_31a.
  pose proof (n4_31 P (¬ Q)) as n4_31b. (*Not cited*)
  apply propositional_extensionality in n4_31b.
  replace (¬ Q ∨ P) with (P ∨ ¬ Q) in n4_7a
    by now apply n4_31b.
  pose proof (n4_3 P Q) as n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q ∧ P) with (P ∧ Q) in n4_7a
    by now apply n4_3a.
  pose proof (n4_21 (P ∧ Q ∨ ¬ Q) (P ∨ ¬ Q)) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ ¬ Q ↔ P ∧ Q ∨ ¬ Q) with 
      (P ∧ Q ∨ ¬ Q ↔ P ∨ ¬ Q) in n4_7a
      by now apply n4_21a.
  exact n4_7a.
Qed.

Theorem n5_63 (P Q : Prop) :
  (P ∨ Q) ↔ (P ∨ (¬ P ∧ Q)).
Proof.
  pose proof (n5_62 Q (¬ P)) as n5_62a.
  pose proof (n4_13 P) as n4_13a. (*Not cited*)
  apply propositional_extensionality in n4_13a.
  replace (¬¬ P) with P in n5_62a
    by now apply n4_13a.
  pose proof (n4_31 P Q) as n4_31a. (*Not cited*)
  apply propositional_extensionality in n4_31a.
  replace (Q ∨ P) with (P ∨ Q) in n5_62a
    by now apply n4_31a.
  pose proof (n4_31 P (Q ∧ ¬ P)) as n4_31b. (*Not cited*)
  apply propositional_extensionality in n4_31b.
  replace ((Q ∧ ¬ P) ∨ P) with (P ∨ (Q ∧ ¬ P)) in n5_62a
    by now apply n4_31b.
  pose proof (n4_21 (P ∨ Q) (P ∨ (Q ∧ ¬ P))) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (P ∨ Q ∧ ¬ P ↔ P ∨ Q) with 
      (P ∨ Q ↔ P ∨ Q ∧ ¬ P) in n5_62a
      by now apply n4_21a.
  pose proof (n4_3 (¬ P) Q) as n4_3a. (*Not cited*)
  apply propositional_extensionality in n4_3a.
  replace (Q ∧ ¬ P) with (¬ P ∧ Q) in n5_62a
    by now apply n4_3a.
  exact n5_62a.
Qed.

Theorem n5_7 (P Q R : Prop) :
  ((P ∨ R) ↔ (Q ∨ R)) ↔ (R ∨ (P ↔ Q)).
Proof.
  pose proof (n4_74 R P) as n4_74a.
  pose proof (n4_74 R Q) as n4_74b. (*Greg's suggestion*)
  Conj n4_74a n4_74b Ca.
  pose proof (Comp3_43 (¬ R) (P ↔ R ∨ P) (Q ↔ R ∨ Q)) as Comp3_43a.
  MP Comp3_43a Ca.
  pose proof (n4_22 P (R ∨ P) (R ∨ Q)) as n4_22a.
  pose proof (n4_22 P (R ∨ Q) Q) as n4_22b.
  pose proof (Exp3_3 (P ↔ (R ∨ Q)) ((R ∨ Q) ↔ Q) (P ↔ Q)) as Exp3_3a.
  MP Exp3_3a n4_22b.
  Syll n4_22a Exp3_3a Sa.
  pose proof (Imp3_31 ((P ↔ (R ∨ P)) ∧
    ((R ∨ P) ↔ (R ∨ Q))) ((R ∨ Q) ↔ Q) (P ↔ Q)) as Imp3_31a.
  MP Imp3_31a Sa.
  pose proof (n4_32 (P ↔ R ∨ P) (R ∨ P ↔ R ∨ Q) (R ∨ Q ↔ Q)) as n4_32a.
  apply propositional_extensionality in n4_32a.
  symmetry in n4_32a.
  replace (((P ↔ (R ∨ P)) ∧ ((R ∨ P) ↔
      (R ∨ Q))) ∧ ((R ∨ Q) ↔ Q)) with 
    ((P ↔ (R ∨ P)) ∧ (((R ∨ P) ↔
      (R ∨ Q)) ∧ ((R ∨ Q) ↔ Q))) in Imp3_31a 
    by now apply n4_32a.
  pose proof (n4_3 (R ∨ Q ↔ Q) (R ∨ P ↔ R ∨ Q)) as n4_3a.
  apply propositional_extensionality in n4_3a.
  replace ((R ∨ P ↔ R ∨ Q) ∧ (R ∨ Q ↔ Q)) with 
    ((R ∨ Q ↔ Q) ∧ (R ∨ P ↔ R ∨ Q)) in Imp3_31a
    by now apply n4_3a.
  pose proof (n4_32 (P ↔ R ∨ P) (R ∨ Q ↔ Q) (R ∨ P ↔ R ∨ Q)) as n4_32b.
  apply propositional_extensionality in n4_32b.
  replace ((P ↔ (R ∨ P)) ∧
      ((R ∨ Q ↔ Q) ∧ (R ∨ P ↔ R ∨ Q))) with 
    (((P ↔ (R ∨ P)) ∧ (R ∨ Q ↔ Q)) ∧
      (R ∨ P ↔ R ∨ Q)) in Imp3_31a
    by now apply n4_32b.
  pose proof (Exp3_3 
    ((P ↔ (R ∨ P)) ∧ (R ∨ Q ↔ Q)) 
    (R ∨ P ↔ R ∨ Q) (P ↔ Q)) as Exp3_3b.
  MP Exp3_3b Imp3_31a.
  pose proof (n4_21 Q (R ∨ Q)) as n4_21a.
  apply propositional_extensionality in n4_21a. 
  symmetry in n4_21a.
  replace (Q ↔ R ∨ Q) with (R ∨ Q ↔ Q) in Comp3_43a
    by now apply n4_21a.
  Syll Comp3_43a Exp3_3b Sb.
  pose proof (n4_31 P R) as n4_31a.
  apply propositional_extensionality in n4_31a.
  replace (R ∨ P) with (P ∨ R) in Sb by now apply n4_31a.
  pose proof (n4_31 Q R) as n4_31b.
  apply propositional_extensionality in n4_31b.
  replace (R ∨ Q) with (Q ∨ R) in Sb by now apply n4_31b.
  pose proof (Imp3_31 (¬ R) (P ∨ R ↔ Q ∨ R) (P ↔ Q)) as Imp3_31b.
  MP Imp3_31b Sb.
  pose proof (n4_3 (P ∨ R ↔ Q ∨ R) (¬ R)) as n4_3b. 
  apply propositional_extensionality in n4_3b.
  replace (¬ R ∧ (P ∨ R ↔ Q ∨ R)) with 
    ((P ∨ R ↔ Q ∨ R) ∧ ¬ R) in Imp3_31b
    by now apply n4_3b.
  pose proof (Exp3_3 
    (P ∨ R ↔ Q ∨ R) (¬ R) (P ↔ Q)) as Exp3_3c.
  MP Exp3_3c Imp3_31b.
  replace (¬ R → (P ↔ Q)) with (¬¬ R ∨ (P ↔ Q)) 
    in Exp3_3c by now rewrite Impl1_01.
  pose proof (n4_13 R) as n4_13a.
  apply propositional_extensionality in n4_13a.
  replace (¬¬ R) with R in Exp3_3c
    by now apply n4_13a.
  pose proof (Add1_3 P R) as Add1_3a.
  pose proof (Add1_3 Q R) as Add1_3b.
  Conj Add1_3a Add1_3b Cb.
  pose proof (Comp3_43 (R) (P ∨ R) (Q ∨ R)) as Comp3_43b.
  MP Comp3_43b Cb.
  pose proof (n5_1 (P ∨ R) (Q ∨ R)) as n5_1a.
  Syll Comp3_43b n5_1a Sc.
  pose proof (n4_37 P Q R) as n4_37a.
  Conj Sc n4_37a Cc.
  pose proof (n4_77 (P ∨ R ↔ Q ∨ R)
    R (P ↔ Q)) as n4_77a.
  rewrite Equiv4_01 in n4_77a.
  pose proof (Simp3_26 
    ((R → P ∨ R ↔ Q ∨ R) ∧
      (P ↔ Q → P ∨ R ↔ Q ∨ R)
    → R ∨ (P ↔ Q) → P ∨ R ↔ Q ∨ R)
    ((R ∨ (P ↔ Q) → P ∨ R ↔ Q ∨ R)
      → (R → P ∨ R ↔ Q ∨ R) ∧
        (P ↔ Q → P ∨ R ↔ Q ∨ R))) as Simp3_26a.
  MP Simp3_26 n4_77a.
  MP Simp3_26a Cc.
  clear n4_77a. clear Cc. clear n4_37a. clear Sa.
    clear n5_1a. clear Comp3_43b. clear Cb. 
    clear Add1_3a. clear Add1_3b. clear Ca. clear Imp3_31b.
    clear n4_74a. clear n4_74b. clear Comp3_43a.
    clear Imp3_31a. clear n4_22a. clear n4_22b. 
    clear Exp3_3a. clear Exp3_3b. clear Sb. clear Sc.
    clear n4_13a. clear n4_3a. clear n4_3b. clear n4_21a.
    clear n4_31a. clear n4_31b. clear n4_32a. clear n4_32b.
  Conj Exp3_3c Simp3_26a Cdd.
  Equiv Cdd.
  exact Cdd.
Qed.

(* pdf, p156, p177 *)
Theorem n5_71 (P Q R : Prop) :
  (Q → ¬ R) → (((P ∨ Q) ∧ R) ↔ (P ∧ R)).
Proof.
  assert (S1 : (P ∨ Q) ∧ R ↔ P ∧ R ∨ Q ∧ R).
  {
    pose proof (n4_4 R P Q) as n4_4.
    (* We simplify the process to split the bidirectional arrows... *)
    replace (R ∧ (P ∨ Q)) with ((P ∨ Q) ∧ R) in n4_4
      by (apply propositional_extensionality; split; apply n3_22).
    replace (R ∧ P) with (P ∧ R) in n4_4 
      by (apply propositional_extensionality; split; apply n3_22).
    replace (R ∧ Q) with (Q ∧ R) in n4_4
      by (apply propositional_extensionality; split; apply n3_22).
    exact n4_4.
  }
  assert (S2 : (Q → ¬ R) → ~(Q ∧ R)).
  {
    pose proof (n4_62 Q R) as n4_62.
    destruct n4_62 as [n4_62l n4_62r].
    pose proof (n4_51 Q R) as n4_51.
    destruct n4_51 as [n4_51l n4_51r].
    clear n4_62r n4_51l.
    Syll n4_62l n4_51r S2.
    exact S2.
  }
  assert (S3 : (Q → ¬ R) → ((P ∧ R ∨ Q ∧ R) ↔ P ∧ R)).
  {
    pose proof (n4_74 (Q ∧ R) (P ∧ R)) as n4_74.
    symmetry in n4_74.
    replace (Q ∧ R ∨ P ∧ R) with (P ∧ R ∨ Q ∧ R) in n4_74
      by (apply propositional_extensionality; split; apply Perm1_4).
    Syll S2 n4_74 S3.
    exact S3.
  }
  assert (S4 : (Q → ¬ R) → (((P ∨ Q) ∧ R) ↔ (P ∧ R))).
  {
    (* This has been very confusing and unrigorous for the proof: the 
      substitution is not done on the whole proposition *)
    intro Hp.
    (* We have to clear everything else just to do the right `Conj` *)
    assert (C1 : ((P ∨ Q) ∧ R ↔ P ∧ R ∨ Q ∧ R) ∧ (P ∧ R ∨ Q ∧ R ↔ P ∧ R)).
    {
      pose proof (S3 Hp) as S3.
      clear Hp S2.
      Conj S3_1 S1 C1.
      exact C1.
    }
    pose proof (n4_22 ((P ∨ Q) ∧ R) (P ∧ R ∨ Q ∧ R)
        (P ∧ R)) as n4_22.
    MP n4_22 C1.
    exact n4_22.
  }
  exact S4.
Qed.

Theorem n5_74 (P Q R : Prop) :
  (P → (Q ↔ R)) ↔ ((P → Q) ↔ (P → R)).
Proof.
  pose proof (n5_41 P Q R) as n5_41a.
  pose proof (n5_41 P R Q) as n5_41b.
  Conj n5_41a n5_41b C.
  pose proof (n4_38 
      ((P → Q) → (P → R)) ((P → R) → (P → Q)) 
      (P → Q → R) (P → R → Q)) as n4_38a.
  MP n4_38a C.
  replace (((P → Q) → (P → R)) ∧ ((P → R) → (P → Q))) 
    with ((P → Q) ↔ (P → R)) in n4_38a
    by now rewrite Equiv4_01.
  pose proof (n4_76 P (Q → R) (R → Q)) as n4_76a.
  replace ((Q → R) ∧ (R → Q)) with (Q ↔ R) in n4_76a
    by now rewrite Equiv4_01.
  apply propositional_extensionality in n4_76a.
  symmetry in n4_76a.
  replace ((P → Q → R) ∧ (P → R → Q)) with 
      (P → (Q ↔ R)) in n4_38a by now apply n4_76a.
  pose proof (n4_21 (P → Q ↔ R) 
    ((P → Q) ↔ (P → R))) as n4_21a. (*Not cited*)
  apply propositional_extensionality in n4_21a.
  replace (((P → Q) ↔ (P → R)) ↔ (P → Q ↔ R)) with 
      ((P → (Q ↔ R)) ↔ ((P → Q) ↔ (P → R))) in n4_38a
      by now apply n4_21a.
  exact n4_38a.
Qed.

Theorem n5_75 (P Q R : Prop) :
  ((R → ¬ Q) ∧ (P ↔ Q ∨ R)) → ((P ∧ ¬ Q) ↔ R).
Proof.
  pose proof (n5_6 P Q R) as n5_6a.
  replace ((P ∧ ¬ Q → R) ↔ (P → Q ∨ R)) with 
      (((P ∧ ¬ Q → R) → (P → Q ∨ R)) ∧
      ((P → Q ∨ R) → (P ∧ ¬ Q → R))) in n5_6a
      by now rewrite Equiv4_01.
  pose proof (Simp3_27 
      ((P ∧ ¬ Q → R) → (P → Q ∨ R)) 
      ((P → Q ∨ R) → (P ∧ ¬ Q → R))) as Simp3_27a.
  MP Simp3_27a n5_6a.
  pose proof (Simp3_26 
    (P → (Q ∨ R)) ((Q ∨ R) → P)) as Simp3_26a.
  replace ((P → (Q ∨ R)) ∧ ((Q ∨ R) → P)) with 
      (P ↔ (Q ∨ R)) in Simp3_26a
      by now rewrite Equiv4_01.
  Syll Simp3_26a Simp3_27a Sa.
  pose proof (Simp3_27 
    (R → ¬ Q) (P ↔ (Q ∨ R))) as Simp3_27b.
  Syll Simp3_27b Sa Sb.
  pose proof (Simp3_27 
    (P → (Q ∨ R)) ((Q ∨ R) → P)) as Simp3_27c.
  replace ((P → (Q ∨ R)) ∧ ((Q ∨ R) → P)) with 
      (P ↔ (Q ∨ R)) in Simp3_27c 
      by now rewrite Equiv4_01.
  Syll Simp3_27b Simp3_27c Sc.
  pose proof (n4_77 P Q R) as n4_77a.
  apply propositional_extensionality in n4_77a.
  replace (Q ∨ R → P) with ((Q → P) ∧ (R → P)) in Sc
    by now apply n4_77a.
  pose proof (Simp3_27 (Q → P) (R → P)) as Simp3_27d.
  Syll Sa Simp3_27d Sd.
  pose proof (Simp3_26 (R → ¬ Q) (P ↔ (Q ∨ R))) as Simp3_26b.
  Conj Sd Simp3_26b Ca.
  pose proof (Comp3_43 
      ((R → ¬ Q) ∧ (P ↔ (Q ∨ R))) (R → P) (R → ¬ Q)) as Comp3_43a.
  MP Comp3_43a Ca.
  pose proof (Comp3_43 R P (¬ Q)) as Comp3_43b.
  Syll Comp3_43a Comp3_43b Se.
  clear n5_6a. clear Simp3_27a. 
  clear Simp3_27c. clear Simp3_27d. 
  clear Simp3_26a.  clear Comp3_43b. 
  clear Simp3_26b. clear Comp3_43a.
  clear Sa. clear Sc. clear Sd. clear Ca. 
  clear n4_77a. clear Simp3_27b. 
  Conj Sb Se Cb.
  pose proof (Comp3_43 
    ((R → ¬ Q) ∧ (P ↔ Q ∨ R)) 
    (P ∧ ¬ Q → R) (R → P ∧ ¬ Q)) as Comp3_43c.
  MP Comp3_43c Cb.
  replace ((P ∧ ¬ Q → R) ∧ (R → P ∧ ¬ Q)) with 
      (P ∧ ¬ Q ↔ R) in Comp3_43c 
      by now rewrite Equiv4_01.
  exact Comp3_43c.
Qed.
